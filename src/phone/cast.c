/* The TV (Cast/CONTRACT.md): our app on a TV answers on this Wi-Fi (UDP 8766, "SBORIGIN?") and takes a phone on
   a WebSocket (8765): paired once with a 4-digit code shown on the TV (its token kept), then told what to play and
   driven like a remote (pause, seek, stop, keys), its state coming back about once a second. A TV whose app is
   closed is found over SSDP (LG's own second-screen service) and the app opened through LG's remote-control channel
   (SSAP, 3000/3001: the TV asks once to allow this phone, its key kept); a TV that is off is woken over Wi-Fi
   (Wake-on-LAN, when the TV allows it). TVs once connected are remembered (never their keys in the repo: in the
   app's own store). Everything stays on the local network. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include <dlfcn.h>
#include <poll.h>
#include <errno.h>
#include <time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <ifaddrs.h>
#include <net/if.h>
#include <curl/curl.h>
#include "phone/phone.h"
#include "ui/orbs.h"
#include <math.h>
#include "ui/gfx.h"
#include "ui/text.h"
#include "ui/icon.h"
#include "ui/widgets.h"
#include "core/app.h"
#include "core/keys.h"
#include "core/hit.h"
#include "core/i18n.h"
#include "core/net.h"
#include "core/store.h"
#include "core/json.h"
#include "core/best.h"
#include "core/stremio.h"
#include "core/subs.h"
#include "ui/img.h"
#include "core/live.h"
#include "ui/subfonts.h"

static double now_s(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec / 1e9; }
#define TV_APP_LG "tv.stremioorigin.app"
#define TV_APP_SAMSUNG "StrOrigTV1.StremioOrigin" /* (its package alone, StrOrigTV1, tried after it) */
#define RX_PORT 8766
enum { K_LG = 1, K_SAMSUNG, K_ANDROID, K_OTHER };
/* a TV's card: what is happening to it */
enum { S_IDLE = 0, S_CONNECTING, S_OPENING, S_WAKING, S_ALLOW, S_PAIR, S_ON, S_FAIL, S_OFF, S_PIN }; /* S_PIN: an LG TV that pairs with a PIN (shown on it, typed here) */
typedef struct { char ip[48], name[96], model[96], loc[256], mac[24], id[64]; int kind, port, origin, state, gone; char err[160]; double stAt, seenAt; } Tv; /* seenAt: when it last answered */ static volatile int linkIdx = -1; /* (the TV linked or being linked: always listed) */ /* gone: not answering the last look (not listed: only what is there now) */ /* origin: our app answered on it; id: the app's own (its token is kept under it) */
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static Tv tvs[16]; static int ntv, scanning, chosen = -1, flowBusy;
static int shOpen, rmOpen; static double shCloseAt; static volatile int lanBlocked; /* a VPN app lets no packet out to this network: said in the sheet */
/* a TV listed (and the button lit) only while it answers: the last scan found it, a minute ago at most (a list from
   before the phone slept is never shown while the next scan runs), or it is the one connected */
static int tv_here(int i) { return i == linkIdx || (!tvs[i].gone && now_s() - tvs[i].seenAt < 60); }
static void set_state(int i, int st, const char *err) { pthread_mutex_lock(&mu); if (i >= 0 && i < ntv) { if (tvs[i].state != st) tvs[i].stAt = now_s(); tvs[i].state = st; snprintf(tvs[i].err, sizeof tvs[i].err, "%s", err ? err : ""); } pthread_mutex_unlock(&mu); }

/* ---- the remembered TVs (name, kind, address, how to wake it, the app's id): shown even when off ---- */
static void remember(const Tv *t) { cJSON *a = store_node("castTvs"); cJSON *arr = cJSON_IsArray(a) ? cJSON_Duplicate(a, 1) : cJSON_CreateArray(); cJSON *e; int i = 0, at = -1;
  cJSON_ArrayForEach(e, arr) { if ((t->id[0] && !strcmp(js_str(e, "id", ""), t->id)) || !strcmp(js_str(e, "ip", ""), t->ip)) at = i; i++; }
  const cJSON *old = at >= 0 ? cJSON_GetArrayItem(arr, at) : NULL; cJSON *o = cJSON_CreateObject();
  const char *keepName = js_str(old, "name", ""); cJSON_AddStringToObject(o, "ip", t->ip); cJSON_AddStringToObject(o, "name", keepName[0] && strcmp(keepName, js_str(old, "ip", "")) ? keepName : t->name); /* (the first real name stays) */ cJSON_AddNumberToObject(o, "kind", t->kind);
  cJSON_AddStringToObject(o, "mac", t->mac[0] ? t->mac : js_str(old, "mac", "")); cJSON_AddStringToObject(o, "id", t->id[0] ? t->id : js_str(old, "id", ""));
  if (at >= 0) cJSON_ReplaceItemInArray(arr, at, o); else cJSON_AddItemToArray(arr, o); store_set_node("castTvs", arr); }
static void forget_all_offline(void) {} /* (Settings > Cast: later) */

/* ---- our app on a TV: "SBORIGIN?" over UDP 8766, its answer one line of JSON ---- */
typedef struct { int ok; char ip[48], id[64], name[96], mac[24]; int port, paired; } Rx;
static void rx_parse(const char *buf, const char *ip, Rx *o) { cJSON *j = cJSON_Parse(buf); if (!j) return; memset(o, 0, sizeof *o); o->ok = 1; snprintf(o->ip, sizeof o->ip, "%s", ip);
  snprintf(o->id, sizeof o->id, "%s", js_str(j, "id", "")); snprintf(o->name, sizeof o->name, "%s", js_str(j, "name", "")); snprintf(o->mac, sizeof o->mac, "%s", js_str(j, "mac", ""));
  o->port = (int)js_num(j, "port", 8765); o->paired = js_bool(j, "paired", 0); cJSON_Delete(j); }
static int rx_probe(const char *ip, int ms, Rx *o) { /* one TV, asked directly */
  memset(o, 0, sizeof *o); int fd = socket(AF_INET, SOCK_DGRAM, 0); if (fd < 0) return 0;
  struct sockaddr_in to; memset(&to, 0, sizeof to); to.sin_family = AF_INET; to.sin_port = htons(RX_PORT); inet_pton(AF_INET, ip, &to.sin_addr);
  sendto(fd, "SBORIGIN?", 9, 0, (struct sockaddr *)&to, sizeof to); double end = now_s() + ms / 1000.0;
  while (now_s() < end && !o->ok) { struct pollfd p = { fd, POLLIN, 0 }; if (poll(&p, 1, 100) <= 0) { if (now_s() + 0.3 < end && (int)((end - now_s()) * 10) % 4 == 0) sendto(fd, "SBORIGIN?", 9, 0, (struct sockaddr *)&to, sizeof to); continue; }
    char buf[1024]; struct sockaddr_in from; socklen_t fl = sizeof from; int n = recvfrom(fd, buf, sizeof buf - 1, 0, (struct sockaddr *)&from, &fl); if (n <= 0) continue; buf[n] = 0; char fip[48]; inet_ntop(AF_INET, &from.sin_addr, fip, sizeof fip); rx_parse(buf, fip, o); }
  close(fd); return o->ok; }

/* ---- finding TVs: our app's answer (UDP broadcast) and LG's/Samsung's own (SSDP), together ---- */
static void parse_desc(Tv *t) {
  size_t len; int st; unsigned char *b = net_fetch_sync(t->loc, &len, &st, 2500); if (!b) return;
  const char *keys[3] = { "friendlyName", "modelName", "manufacturer" }; char *dst[3] = { t->name, t->model, NULL }; char man[96] = "";
  for (int k = 0; k < 3; k++) { char open[48]; snprintf(open, sizeof open, "<%s>", keys[k]); char *p = strstr((char *)b, open); if (!p) continue; p += strlen(open); char *e = strchr(p, '<'); if (!e) continue;
    char *d = k < 2 ? dst[k] : man; size_t n = (size_t)(e - p); if (n > 95) n = 95; memcpy(d, p, n); d[n] = 0; }
  if (!t->kind) t->kind = strstr(man, "LG") ? K_LG : strstr(man, "Samsung") ? K_SAMSUNG : strstr((char *)b, "Android") || strstr((char *)b, "Google") || strstr((char *)b, "BRAVIA") || strstr((char *)b, "SHIELD") || strstr(man, "Amazon") ? K_ANDROID : K_OTHER;
  if (t->kind == K_SAMSUNG && !strncmp(t->name, "[TV] ", 5)) memmove(t->name, t->name + 5, strlen(t->name + 5) + 1);
  free(b);
}
/* ---- Android TV and Google TV, our app open or not: Google's TV remote service announces itself over mDNS
   (_androidtvremote2._tcp, the older one _androidtvremote._tcp); the box's name is its service's name ---- */
static int mdns_query(unsigned char *q, int qu) { static const char *svc[2] = { "_androidtvremote2", "_androidtvremote" }; int n = 12; memset(q, 0, 12); q[5] = 2; /* (id 0, a standard query, two questions) */
  for (int i = 0; i < 2; i++) { const char *lab[3] = { svc[i], "_tcp", "local" }; for (int k = 0; k < 3; k++) { int l = (int)strlen(lab[k]); q[n++] = (unsigned char)l; memcpy(q + n, lab[k], l); n += l; } q[n++] = 0; q[n++] = 0; q[n++] = 12; q[n++] = qu ? 0x80 : 0; q[n++] = 1; } /* PTR, IN, answered to this socket (unicast) or, asked from 5353, to the group (multicast) */
  return n; }
static int dns_name(const unsigned char *m, int len, int at, char *out, int cap, int firstOnly) { int o = 0, jumped = 0, end = -1, hops = 0; if (cap) out[0] = 0;
  while (at < len && hops < 32) { int l = m[at]; if (!l) { if (end < 0) end = at + 1; break; }
    if ((l & 0xc0) == 0xc0) { if (at + 1 >= len) return -1; if (end < 0) end = at + 2; at = ((l & 0x3f) << 8) | m[at + 1]; jumped = 1; hops++; continue; }
    if (at + 1 + l > len) return -1; if (o + l + 2 < cap && !(firstOnly && o)) { if (o) out[o++] = '.'; memcpy(out + o, m + at + 1, l); o += l; out[o] = 0; } at += 1 + l; }
  (void)jumped; return end; }
/* an answer naming an Android TV remote service: 1 and its name (the PTR's instance, its first label) */
static int mdns_atv(const unsigned char *m, int len, char *name, int cap) {
  if (len < 12 || !(m[2] & 0x80)) return 0; /* (answers only: on 5353 another phone's question comes in too, its known answers naming a TV that is not it) */ int qd = m[4] << 8 | m[5], an = (m[6] << 8 | m[7]) + (m[8] << 8 | m[9]) + (m[10] << 8 | m[11]), at = 12; char nm[256];
  for (int i = 0; i < qd && at > 0; i++) { at = dns_name(m, len, at, nm, sizeof nm, 0); if (at < 0) return 0; at += 4; }
  for (int i = 0; i < an && at > 0 && at + 10 <= len; i++) { at = dns_name(m, len, at, nm, sizeof nm, 0); if (at < 0 || at + 10 > len) return 0;
    int ty = m[at] << 8 | m[at + 1], rl = m[at + 8] << 8 | m[at + 9], rd = at + 10; if (rd + rl > len) return 0;
    if (strcasestr(nm, "_androidtvremote")) { if (ty == 12) { dns_name(m, len, rd, name, cap, 1); return 1; } if (ty == 33 || ty == 16) { char in[128]; snprintf(in, sizeof in, "%s", nm); char *d = strstr(in, "._androidtvremote"); if (d) { *d = 0; snprintf(name, cap, "%s", in); } return 1; } }
    at = rd + rl; }
  return 0; }
static void *scan_thread(void *a) { (void)a;
  pplat_multicast(1);
  int fd = socket(AF_INET, SOCK_DGRAM, 0), rf = socket(AF_INET, SOCK_DGRAM, 0), md = socket(AF_INET, SOCK_DGRAM, 0); unsigned char mq[128]; int mql = mdns_query(mq, 1), ttl0 = 255;
  struct sockaddr_in mto; memset(&mto, 0, sizeof mto); mto.sin_family = AF_INET; mto.sin_port = htons(5353); inet_pton(AF_INET, "224.0.0.251", &mto.sin_addr); if (md >= 0) setsockopt(md, IPPROTO_IP, IP_MULTICAST_TTL, &ttl0, sizeof ttl0); if (fd < 0 || rf < 0) { if (fd >= 0) close(fd); if (rf >= 0) close(rf); pthread_mutex_lock(&mu); scanning = 0; pthread_mutex_unlock(&mu); pplat_multicast(0); return NULL; }
  int ttl = 2, on = 1; setsockopt(fd, IPPROTO_IP, IP_MULTICAST_TTL, &ttl, sizeof ttl); setsockopt(rf, SOL_SOCKET, SO_BROADCAST, &on, sizeof on);
  /* the same question asked from mDNS's own port too (5353, shared with the phone's own responder), its answer to the group: Android 14's
     responder (a Google TV) answers no question from another port (RFC 6762's "legacy unicast", md's), older boxes answer both */
  int m5 = socket(AF_INET, SOCK_DGRAM, 0); unsigned char mq5[128]; int mq5l = mdns_query(mq5, 0); if (m5 >= 0) { struct sockaddr_in b5; memset(&b5, 0, sizeof b5); b5.sin_family = AF_INET; b5.sin_port = htons(5353); setsockopt(m5, SOL_SOCKET, SO_REUSEADDR, &on, sizeof on);
#ifdef SO_REUSEPORT
    setsockopt(m5, SOL_SOCKET, SO_REUSEPORT, &on, sizeof on);
#endif
    if (bind(m5, (struct sockaddr *)&b5, sizeof b5) < 0) { fprintf(stderr, "[cast] mDNS: port 5353 not shared (%d): the other port's question only\n", errno); close(m5); m5 = -1; } else setsockopt(m5, IPPROTO_IP, IP_MULTICAST_TTL, &ttl0, sizeof ttl0); }
  struct sockaddr_in to; memset(&to, 0, sizeof to); to.sin_family = AF_INET; to.sin_port = htons(1900); inet_pton(AF_INET, "239.255.255.250", &to.sin_addr);
  struct sockaddr_in bc; memset(&bc, 0, sizeof bc); bc.sin_family = AF_INET; bc.sin_port = htons(RX_PORT); inet_pton(AF_INET, "255.255.255.255", &bc.sin_addr);
  static const char *ST[3] = { "urn:lge-com:service:webos-second-screen:1", "urn:samsung.com:device:RemoteControlReceiver:1", "urn:dial-multiscreen-org:service:dial:1" };
  for (int round = 0; round < 2; round++) { for (int i = 0; i < 3; i++) { char m[400]; int n = snprintf(m, sizeof m, "M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\nMAN: \"ssdp:discover\"\r\nMX: 2\r\nST: %s\r\n\r\n", ST[i]); sendto(fd, m, n, 0, (struct sockaddr *)&to, sizeof to); }
    sendto(rf, "SBORIGIN?", 9, 0, (struct sockaddr *)&bc, sizeof bc); if (md >= 0) sendto(md, mq, mql, 0, (struct sockaddr *)&mto, sizeof mto); }
  /* every address of this phone's own network, asked directly too: a VPN app on the phone, or the TV itself, may let
     no broadcast or multicast through (254 small packets) */
  { struct ifaddrs *ifs = NULL; if (!getifaddrs(&ifs)) { for (struct ifaddrs *f = ifs; f; f = f->ifa_next) { if (!f->ifa_addr || f->ifa_addr->sa_family != AF_INET || !f->ifa_netmask || (f->ifa_flags & IFF_LOOPBACK)) continue;
      unsigned ip = ntohl(((struct sockaddr_in *)f->ifa_addr)->sin_addr.s_addr), mask = ntohl(((struct sockaddr_in *)f->ifa_netmask)->sin_addr.s_addr); if (!mask || ~mask > 1022 || ~mask < 3) continue; /* (a /22 at most; never a one-address tunnel: a VPN's) */
      if (!((ip >> 24) == 10 || (ip >> 20) == (172u << 4 | 1) || (ip >> 16) == (192u << 8 | 168))) continue; /* (a home network only) */
      if (m5 >= 0) { struct ip_mreq mr; memset(&mr, 0, sizeof mr); mr.imr_multiaddr = mto.sin_addr; mr.imr_interface.s_addr = htonl(ip); setsockopt(m5, IPPROTO_IP, IP_ADD_MEMBERSHIP, &mr, sizeof mr); setsockopt(m5, IPPROTO_IP, IP_MULTICAST_IF, &mr.imr_interface, sizeof mr.imr_interface); sendto(m5, mq5, mq5l, 0, (struct sockaddr *)&mto, sizeof mto); } /* (the group on this network's interface: never the mobile one's) */
      unsigned net = ip & mask, last = net | ~mask; int blocked = 0; static const char SSDP_LG[] = "M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\nMAN: \"ssdp:discover\"\r\nMX: 1\r\nST: urn:lge-com:service:webos-second-screen:1\r\n\r\n";
      for (unsigned h = net + 1; h < last; h++) { if (h == ip) continue; struct sockaddr_in d; memset(&d, 0, sizeof d); d.sin_family = AF_INET; d.sin_addr.s_addr = htonl(h);
        d.sin_port = htons(RX_PORT); if (sendto(rf, "SBORIGIN?", 9, 0, (struct sockaddr *)&d, sizeof d) < 0 && errno == EPERM) blocked = 1; d.sin_port = htons(1900); sendto(fd, SSDP_LG, sizeof SSDP_LG - 1, 0, (struct sockaddr *)&d, sizeof d); if (md >= 0) { d.sin_port = htons(5353); sendto(md, mq, mql, 0, (struct sockaddr *)&d, sizeof d); } } /* (an mDNS question to each too: a responder answers one sent to it) */
      if (m5 >= 0) sendto(m5, mq5, mq5l, 0, (struct sockaddr *)&mto, sizeof mto); /* (once more: a lost packet) */
      lanBlocked = blocked; if (blocked) fprintf(stderr, "[cast] this phone may not talk to its own network (a VPN app blocks it)\n"); break; } freeifaddrs(ifs); } }
  /* the remembered TVs, asked directly too (a broadcast may not cross every router) */
  { const cJSON *kn = store_node("castTvs"), *e; if (cJSON_IsArray(kn)) cJSON_ArrayForEach(e, kn) { struct sockaddr_in d; memset(&d, 0, sizeof d); d.sin_family = AF_INET; d.sin_port = htons(RX_PORT); if (inet_pton(AF_INET, js_str(e, "ip", ""), &d.sin_addr) == 1) sendto(rf, "SBORIGIN?", 9, 0, (struct sockaddr *)&d, sizeof d); } }
  double end = now_s() + 3.5, again = now_s() + 1.2; Tv found[16]; int nf = 0;
  while (now_s() < end) { struct pollfd p[4] = { { fd, POLLIN, 0 }, { rf, POLLIN, 0 }, { md, md >= 0 ? POLLIN : 0, 0 }, { m5, m5 >= 0 ? POLLIN : 0, 0 } }; if (now_s() > again) { again = end + 1; sendto(rf, "SBORIGIN?", 9, 0, (struct sockaddr *)&bc, sizeof bc); } if (poll(p, 4, 200) <= 0) continue; /* (a closed one, -1: skipped) */
    for (int s = 0; s < 4; s++) { if (!(p[s].revents & POLLIN)) continue; char buf[2048]; struct sockaddr_in from; socklen_t fl = sizeof from; int n = recvfrom(p[s].fd, buf, sizeof buf - 1, 0, (struct sockaddr *)&from, &fl); if (n <= 0) continue; buf[n] = 0;
      char atvName[96] = ""; if (s >= 2 && !mdns_atv((const unsigned char *)buf, n, atvName, sizeof atvName)) continue; /* (mDNS: only an Android TV's remote service) */
      char ip[48]; inet_ntop(AF_INET, &from.sin_addr, ip, sizeof ip); int k; for (k = 0; k < nf; k++) if (!strcmp(found[k].ip, ip)) break;
      if (k == nf && nf < 16) { memset(&found[nf], 0, sizeof found[nf]); snprintf(found[nf].ip, sizeof found[nf].ip, "%s", ip); nf++; } if (k >= nf) continue; Tv *t = &found[k];
      if (s >= 2) { t->kind = K_ANDROID; if (!t->name[0] && atvName[0]) snprintf(t->name, sizeof t->name, "%s", atvName); continue; } /* an Android TV or Google TV, our app open on it or not */
      if (s == 1) { Rx r; rx_parse(buf, ip, &r); if (!r.ok) continue; t->origin = 1; t->port = r.port; snprintf(t->id, sizeof t->id, "%s", r.id); if (r.name[0]) snprintf(t->name, sizeof t->name, "%s", r.name); if (r.mac[0]) snprintf(t->mac, sizeof t->mac, "%s", r.mac); if (!t->kind || t->kind == K_OTHER) t->kind = strstr(buf, "\"plat\":\"tizen\"") ? K_SAMSUNG : strstr(buf, "\"plat\":\"webos\"") ? K_LG : strstr(buf, "androidtv") ? K_ANDROID : K_OTHER; /* (what our app says it runs on: webOS, Tizen, Android TV; a computer's preview: none of them) */ continue; }
      char *loc = strcasestr(buf, "\nLOCATION:"); char *st = strcasestr(buf, "\nST:");
      if (st && strstr(st, "lge-com")) t->kind = K_LG; else if (st && strstr(st, "samsung.com") && (!t->kind || t->kind == K_OTHER)) t->kind = K_SAMSUNG;
      char *sv = strcasestr(buf, "\nSERVER:"); if (sv && (!t->kind || t->kind == K_OTHER)) { char ln[160]; snprintf(ln, sizeof ln, "%.*s", (int)strcspn(sv + 1, "\r\n"), sv + 1); if (strcasestr(ln, "android")) t->kind = K_ANDROID; } /* (DIAL from an Android kernel, "Linux/5.15-android14": a Google TV whose description names only its maker; never "Chromecast" alone, a dongle with no remote service) */
      if (loc && (!t->loc[0] || (st && strstr(st, "lge-com")))) { loc += 10; while (*loc == ' ') loc++; size_t l = strcspn(loc, "\r\n"); if (l > 255) l = 255; memcpy(t->loc, loc, l); t->loc[l] = 0; } } }
  close(fd); close(rf); if (md >= 0) close(md); if (m5 >= 0) close(m5); pplat_multicast(0);
  for (int k = 0; k < nf; k++) { char nm[96]; snprintf(nm, sizeof nm, "%s", found[k].name); found[k].name[0] = 0; if (found[k].loc[0]) parse_desc(&found[k]); /* the TV's own name first (what its owner sees), our app's next */
    if (!found[k].name[0]) snprintf(found[k].name, sizeof found[k].name, "%s", nm[0] ? nm : found[k].ip);
    if (!strncmp(found[k].name, "[LG] ", 5) || !strncmp(found[k].name, "[TV] ", 5)) memmove(found[k].name, found[k].name + 5, strlen(found[k].name + 5) + 1); }
  pthread_mutex_lock(&mu);
  for (int k = 0; k < nf; k++) { if ((found[k].kind == K_OTHER || !found[k].kind) && !found[k].origin) continue;
    int j; for (j = 0; j < ntv; j++) if (!strcmp(tvs[j].ip, found[k].ip) || (found[k].id[0] && !strcmp(tvs[j].id, found[k].id))) break;
    if (j == ntv && ntv < 16) { tvs[ntv] = found[k]; tvs[ntv].stAt = now_s(); { const cJSON *kn = store_node("castTvs"), *e; if (cJSON_IsArray(kn)) cJSON_ArrayForEach(e, kn) if (!strcmp(js_str(e, "ip", ""), found[k].ip) || (found[k].id[0] && !strcmp(js_str(e, "id", ""), found[k].id))) { const char *n2 = js_str(e, "name", ""); if (*n2 && strcmp(n2, found[k].ip)) snprintf(tvs[ntv].name, sizeof tvs[ntv].name, "%s", n2); } } ntv++; }
    else if (j < ntv) { Tv o = tvs[j]; tvs[j] = found[k]; if (o.name[0] && strcmp(o.name, o.ip)) snprintf(tvs[j].name, sizeof tvs[j].name, "%s", o.name); /* (its name once known stays: never swapped as it comes and goes) */ if (!tvs[j].mac[0]) snprintf(tvs[j].mac, sizeof tvs[j].mac, "%s", o.mac); if (!tvs[j].id[0]) snprintf(tvs[j].id, sizeof tvs[j].id, "%s", o.id); tvs[j].state = o.state == S_OFF ? S_IDLE : o.state; tvs[j].stAt = o.state == S_OFF ? now_s() : o.stAt; snprintf(tvs[j].err, sizeof tvs[j].err, "%s", o.state == S_OFF ? "" : o.err); } }
  for (int j = 0; j < ntv; j++) { int f = 0; for (int k = 0; k < nf; k++) if (!strcmp(tvs[j].ip, found[k].ip) || (found[k].id[0] && !strcmp(tvs[j].id, found[k].id))) f = 1; int keep = j == linkIdx; tvs[j].gone = !f && !keep; if (f) tvs[j].seenAt = now_s(); } /* (only what answered now, and the one connected) */
  fprintf(stderr, "[cast] %d TV(s) answered, %d listed\n", nf, ntv); for (int k = 0; k < ntv; k++) fprintf(stderr, "[cast]  TV %d: %s%s, state %d\n", k + 1, tvs[k].kind == K_LG ? "LG" : tvs[k].kind == K_ANDROID ? "Android TV" : tvs[k].kind == K_SAMSUNG ? "Samsung" : "other", tvs[k].origin ? ", our app answering" : "", tvs[k].state);
  scanning = 0; pthread_mutex_unlock(&mu); return NULL;
}
static void scan(void) { pthread_mutex_lock(&mu); int go = !scanning; scanning = 1; pthread_mutex_unlock(&mu); if (!go) return; pthread_t th; if (pthread_create(&th, NULL, scan_thread, NULL) == 0) pthread_detach(th); else scanning = 0; }

/* ---- WebSockets (curl's, found at run time: older curls have none) ---- */
typedef CURLcode (*WsSend)(CURL *, const void *, size_t, size_t *, curl_off_t, unsigned int);
typedef CURLcode (*WsRecv)(CURL *, void *, size_t, size_t *, const struct curl_ws_frame **);
static WsSend wsSend; static WsRecv wsRecv;
static int ws_load(void) { if (!wsSend) { *(void **)&wsSend = dlsym(RTLD_DEFAULT, "curl_ws_send"); *(void **)&wsRecv = dlsym(RTLD_DEFAULT, "curl_ws_recv"); } return wsSend && wsRecv; }
static int ws_text(CURL *c, const char *s) { size_t sent; return wsSend(c, s, strlen(s), &sent, 0, CURLWS_TEXT) == CURLE_OK; }
/* the next whole message (in buf), NULL after ms; *dead set when the connection is gone */
static char *ws_next(CURL *c, int ms, char *buf, size_t cap, int *dead) {
  static char *pb; static size_t ph; if (pb != buf) { pb = buf; ph = 0; } /* (a message that comes in pieces over several calls: what came is kept, never read again as a new one) */
  size_t have = ph; double end = now_s() + ms / 1000.0; if (dead) *dead = 0;
  while (now_s() < end) { size_t got = 0; const struct curl_ws_frame *f = NULL; CURLcode r = wsRecv(c, buf + have, cap - 1 - have, &got, &f);
    if (r == CURLE_AGAIN) { usleep(30000); continue; } if (r != CURLE_OK) { ph = 0; if (dead) *dead = 1; return NULL; }
    have += got; if (f && (f->flags & CURLWS_CLOSE)) { ph = 0; if (dead) *dead = 1; return NULL; } if (f && f->bytesleft == 0 && (f->flags & CURLWS_TEXT)) { buf[have] = 0; ph = 0; return buf; } if (have >= cap - 1) have = 0; }
  ph = have; return NULL;
}
static CURL *ws_open(const char *url, int ms) { if (!ws_load()) return NULL; CURL *c = curl_easy_init(); if (!c) return NULL;
  curl_easy_setopt(c, CURLOPT_URL, url); curl_easy_setopt(c, CURLOPT_CONNECT_ONLY, 2L); curl_easy_setopt(c, CURLOPT_SSL_VERIFYPEER, 0L); curl_easy_setopt(c, CURLOPT_SSL_VERIFYHOST, 0L); curl_easy_setopt(c, CURLOPT_CONNECTTIMEOUT_MS, (long)ms);
  if (curl_easy_perform(c) == CURLE_OK) return c; curl_easy_cleanup(c); return NULL; }

/* ---- the connection to our app on the TV: one at a time, its own thread ---- */
enum { CX_OFF = 0, CX_CONNECTING, CX_PAIR, CX_READY };
static struct { int st, stop, codeSet, tokBad, wrong, locked; char ip[48], id[64], name[96], tok[80], tokNew[80], code[8], err[160]; int port, tvIdx;
  char *q[24]; int qn; /* what to send */
  char ts[16], title[200]; double pos, dur, stAt, posAt;
  int pw, pwT; struct { char id[64], label[96], lang[16], from[64]; } subs[200], auds[16]; /* (every subtitle the TV lists: its file's, OpenSubtitles' (often dozens), then each addon's, which came last and were cut at 48) */ int nsub, naud, delay, scope, pics, subAr; char sub[64], aud[64]; int tvBest; char ptype[16], pid[96], pvid[96], pinfo[96]; struct { char t[100], i[16]; int b, sep; } chip[8]; int nchip; char p2p[160], syncSt[120]; int canSync, syncing; unsigned pgen; } CX; /* chip: the TV player's own info line */ /* ptype/pid/pvid: what the TV says it plays (pgen moves when it changes) */ /* tvBest: the TV finds the best stream itself (its "ready" says it can) */ /* the film's subtitles and sound tracks on the TV (its own and the addons'), and which are on */
static char chErr[200]; /* (the TV's words for a channel it could not play: a toast on the main thread) */ static double wantAt; static char wantTs[16]; static volatile int notifyNow; /* the play/pause just asked for, when (shown at once, held until the TV says so) */
static void cx_send(const char *s) { pthread_mutex_lock(&mu); if (CX.qn < 24) CX.q[CX.qn++] = strdup(s); pthread_mutex_unlock(&mu); }
static void *cx_thread(void *a) { (void)a; char url[96]; pthread_mutex_lock(&mu); snprintf(url, sizeof url, "ws://%s:%d", CX.ip, CX.port ? CX.port : 8765); char tok[80]; snprintf(tok, sizeof tok, "%s", CX.tok); pthread_mutex_unlock(&mu);
  CURL *c = ws_open(url, 4000); if (!c) { pthread_mutex_lock(&mu); CX.st = CX_OFF; snprintf(CX.err, sizeof CX.err, "%s", T("Could not connect to the TV")); pthread_mutex_unlock(&mu); return NULL; }
  static char m[65536]; /* (the TV's tracks: dozens of subtitles from the addons, well past 4 KB) */
  if (tok[0]) { snprintf(m, sizeof m, "{\"t\":\"hello\",\"token\":\"%s\"}", tok); ws_text(c, m); } else { ws_text(c, "{\"t\":\"pair\"}"); pthread_mutex_lock(&mu); CX.st = CX_PAIR; pthread_mutex_unlock(&mu); }
  while (1) { pthread_mutex_lock(&mu); int stop = CX.stop; char *out[24]; int no = CX.qn; memcpy(out, CX.q, sizeof out); CX.qn = 0; int cs = CX.codeSet; char code[8]; snprintf(code, sizeof code, "%s", CX.code); CX.codeSet = 0; pthread_mutex_unlock(&mu);
    if (stop) { for (int i = 0; i < no; i++) free(out[i]); break; }
    for (int i = 0; i < no; i++) { ws_text(c, out[i]); free(out[i]); }
    if (cs) { snprintf(m, sizeof m, "{\"t\":\"pair\",\"code\":\"%s\"}", code); ws_text(c, m); }
    { static double pingAt; if (now_s() - pingAt > 10) { pingAt = now_s(); size_t sent; wsSend(c, "", 0, &sent, 0, CURLWS_PING); } } /* (a ping now and then: routers and the phone keep a quiet connection open) */
    int dead = 0; char *r = ws_next(c, 120, m, sizeof m, &dead); if (dead) break; if (!r) continue;
    cJSON *j = cJSON_Parse(r); if (!j) continue; const char *t = js_str(j, "t", "");
    pthread_mutex_lock(&mu);
    if (!strcmp(t, "paired")) { snprintf(CX.tokNew, sizeof CX.tokNew, "%s", js_str(j, "token", "")); char h[160]; snprintf(h, sizeof h, "{\"t\":\"hello\",\"token\":\"%s\"}", CX.tokNew); pthread_mutex_unlock(&mu); ws_text(c, h); pthread_mutex_lock(&mu); }
    else if (!strcmp(t, "ready")) { CX.st = CX_READY; CX.tvBest = 0; { const cJSON *cp, *ca = cJSON_GetObjectItemCaseSensitive(j, "caps"); cJSON_ArrayForEach(cp, ca) if (cJSON_IsString(cp) && !strcmp(cp->valuestring, "best")) CX.tvBest = 1; } if (!CX.name[0]) { const char *nm = js_str(j, "name", ""); if (*nm) snprintf(CX.name, sizeof CX.name, "%s", nm); } }
    else if (!strcmp(t, "denied")) { if (CX.st != CX_PAIR) CX.tokBad = 1; snprintf(CX.err, sizeof CX.err, "%s", T("The TV did not accept this phone")); }
    else if (!strcmp(t, "state")) { { const char *ns = js_str(j, "s", ""); int stale = wantAt > 0 && now_s() - wantAt < 2.5 && wantTs[0] && strcmp(ns, wantTs) && (!strcmp(ns, "playing") || !strcmp(ns, "paused")); if (!stale) { snprintf(CX.ts, sizeof CX.ts, "%s", ns); if (!strcmp(ns, wantTs)) wantAt = 0; } } /* (a pause or play just pressed: an older state on its way never flips it back) */ CX.pos = js_num(j, "pos", 0); CX.dur = js_num(j, "dur", 0); CX.posAt = now_s(); const char *ti = js_str(j, "title", ""); if (*ti) snprintf(CX.title, sizeof CX.title, "%s", ti);
      { const cJSON *pv = cJSON_GetObjectItemCaseSensitive(j, "previews"); CX.pw = cJSON_IsObject(pv) ? (int)js_num(pv, "pct", 0) : -1; CX.pwT = cJSON_IsObject(pv) ? (int)js_num(pv, "target", 80) : 0; } /* (the TV waiting for the film's seek previews: how far of the share it waits for; -1 not waiting) */ snprintf(CX.pinfo, sizeof CX.pinfo, "%s", js_str(j, "info", "")); snprintf(CX.p2p, sizeof CX.p2p, "%s", js_str(j, "p2p", "")); if (cJSON_GetObjectItemCaseSensitive(j, "syncing")) { CX.syncing = (int)js_num(j, "syncing", 0); snprintf(CX.syncSt, sizeof CX.syncSt, "%s", js_str(j, "syncSt", "")); } { const cJSON *ca = js_arr(j, "chips"), *e; CX.nchip = 0; if (ca) cJSON_ArrayForEach(e, ca) { if (CX.nchip >= 8) break; snprintf(CX.chip[CX.nchip].t, 100, "%s", js_str(e, "t", "")); snprintf(CX.chip[CX.nchip].i, 16, "%s", js_str(e, "i", "")); CX.chip[CX.nchip].b = (int)js_num(e, "b", 0); CX.chip[CX.nchip].sep = (int)js_num(e, "sep", 0); CX.nchip++; } } /* (the stream in a few words: the remote's chips) */
      { const char *pi = js_str(j, "id", ""), *pv = js_str(j, "vid", ""); if (*pi && (strcmp(pi, CX.pid) || strcmp(pv, CX.pvid))) { snprintf(CX.ptype, sizeof CX.ptype, "%s", js_str(j, "type", "")); snprintf(CX.pid, sizeof CX.pid, "%s", pi); snprintf(CX.pvid, sizeof CX.pvid, "%s", pv); CX.pgen++; } } } /* (another title or episode on the TV, picked with its own remote: the phone follows) */
    else if (!strcmp(t, "tracks")) { const cJSON *a, *e; int k = 0; a = js_arr(j, "subs"); if (a) cJSON_ArrayForEach(e, a) { if (k >= 200) break; snprintf(CX.subs[k].id, 64, "%s", js_str(e, "id", "")); snprintf(CX.subs[k].label, 96, "%s", js_str(e, "label", "")); snprintf(CX.subs[k].lang, 16, "%s", js_str(e, "lang", "")); snprintf(CX.subs[k].from, 64, "%s", js_str(e, "from", "")); k++; } CX.nsub = k;
      k = 0; a = js_arr(j, "audio"); if (a) cJSON_ArrayForEach(e, a) { if (k >= 16) break; snprintf(CX.auds[k].id, 64, "%s", js_str(e, "id", "")); snprintf(CX.auds[k].label, 96, "%s", js_str(e, "label", "")); snprintf(CX.auds[k].lang, 16, "%s", js_str(e, "lang", "")); k++; } CX.naud = k;
      snprintf(CX.sub, sizeof CX.sub, "%s", js_str(j, "sub", "off")); snprintf(CX.aud, sizeof CX.aud, "%s", js_str(j, "aud", "")); CX.delay = (int)js_num(j, "delay", 0); CX.canSync = (int)js_num(j, "canSync", 0); CX.scope = (int)js_num(j, "scope", 0); CX.pics = (int)js_num(j, "pics", 0); /* (a TV that tells what its subtitles can take; an older one: all) */
      if (cJSON_GetObjectItemCaseSensitive(j, "subAr")) CX.subAr = (int)js_num(j, "subAr", 0); else { CX.subAr = 0; for (int q = 0; q < CX.nsub; q++) if (!strcmp(CX.subs[q].id, CX.sub)) { const char *l = CX.subs[q].lang; CX.subAr = !strncasecmp(l, "ar", 2); } } /* (an older TV: the track's language) */ if (cJSON_GetObjectItemCaseSensitive(j, "syncing")) { CX.syncing = (int)js_num(j, "syncing", 0); snprintf(CX.syncSt, sizeof CX.syncSt, "%s", js_str(j, "syncSt", "")); } } /* (a TV that tells Sync with its tracks, as d23efc8 does) */
    else if (!strcmp(t, "error") && *js_str(j, "code", "")) { snprintf(chErr, sizeof chErr, "%s", js_str(j, "msg", "")); } /* (a channel sent from here that the TV could not play: its words, shown here) */
    else if (!strcmp(t, "error")) { const char *em = js_str(j, "msg", ""); snprintf(CX.err, sizeof CX.err, "%s", em); if (CX.st == CX_PAIR) { if (strstr(em, "lock")) CX.locked = 1; else CX.wrong++; } }
    pthread_mutex_unlock(&mu); cJSON_Delete(j);
    if (!strcmp(t, "denied")) break; }
  curl_easy_cleanup(c); pthread_mutex_lock(&mu); int was = CX.st; CX.st = CX_OFF; for (int i = 0; i < CX.qn; i++) free(CX.q[i]); CX.qn = 0; if (was == CX_READY && !CX.stop) snprintf(CX.err, sizeof CX.err, "%s", T("The TV went away")); pthread_mutex_unlock(&mu); return NULL; }
/* start talking to the app on a TV (main thread: the token comes from the store) */
static void cx_start(int i, const Rx *r) { pthread_mutex_lock(&mu); CX.stop = 1; pthread_mutex_unlock(&mu); usleep(150000);
  pthread_mutex_lock(&mu); CX.stop = 0; CX.st = CX_CONNECTING; CX.pw = -1; CX.codeSet = 0; CX.tokBad = 0; CX.wrong = 0; CX.locked = 0; CX.code[0] = 0; CX.err[0] = 0; CX.ts[0] = 0; CX.title[0] = 0; CX.pos = CX.dur = 0; CX.tvIdx = i; CX.nsub = CX.naud = 0; CX.sub[0] = CX.aud[0] = 0; CX.delay = 0;
  snprintf(CX.ip, sizeof CX.ip, "%s", r->ip); snprintf(CX.id, sizeof CX.id, "%s", r->id); CX.port = r->port; snprintf(CX.name, sizeof CX.name, "%s", i >= 0 && i < ntv && tvs[i].name[0] ? tvs[i].name : r->name[0] ? r->name : r->ip); pthread_mutex_unlock(&mu);
  char k[96]; snprintf(k, sizeof k, "casttok_%s", r->id); snprintf(CX.tok, sizeof CX.tok, "%s", store_get(k, ""));
  pthread_t th; if (pthread_create(&th, NULL, cx_thread, NULL) == 0) pthread_detach(th); else CX.st = CX_OFF; }

/* ---- LG: its remote-control channel (SSAP): register once (the TV asks), then open our app ---- */
static char newKey[128], newKeyIp[48], newMac[24], newMacIp[48]; static int newKeySam; /* newKeySam: the key is a Samsung's token */   /* learnt by a thread, kept by the main thread */
static char ssapPin[12]; static volatile int ssapPinSet, ssapPinWait;
static char atvCode[8]; static volatile int atvCodeSet, atvCodeWait, atvWrong; /* an Android TV pairing: its 6-character code typed here */ /* an LG TV pairing with a PIN: typed on the phone, sent by the thread */
static const char *MANIFEST = "{\"manifestVersion\":1,\"appVersion\":\"0.1\",\"signed\":{\"appId\":\"app.stremioorigin.phone\",\"vendorId\":\"app.stremioorigin\",\"localizedAppNames\":{\"\":\"Stremio Origin\"},\"permissions\":[\"LAUNCH\",\"LAUNCH_WEBAPP\",\"APP_TO_APP\",\"READ_RUNNING_APPS\",\"READ_INSTALLED_APPS\",\"CONTROL_POWER\"],\"serial\":\"0\"},"
  "\"permissions\":[\"LAUNCH\",\"LAUNCH_WEBAPP\",\"APP_TO_APP\",\"READ_RUNNING_APPS\",\"READ_INSTALLED_APPS\",\"CONTROL_POWER\"]}";
static CURL *lg_open(const char *ip, int ms) { const char *urls[2] = { "ws://%s:3000", "wss://%s:3001" }; for (int k = 0; k < 2; k++) { char u[96]; snprintf(u, sizeof u, urls[k], ip); CURL *c = ws_open(u, ms); if (c) return c; } return NULL; }
/* 1 opened, 0 failed (err set) */
static int lg_launch(int i, CURL *c, const char *ip, const char *key0, char *err, size_t ecap) { char m[65536]; int dead; char key[128]; snprintf(key, sizeof key, "%s", key0);
  /* register: with the on-screen "allow" first; a TV that refuses that pairs with a PIN it shows (typed on the phone) */
  int pin = 0;
  regAgain: { char *reg = malloc(4096); snprintf(reg, 4096, "{\"type\":\"register\",\"id\":\"reg%d\",\"payload\":{\"forcePairing\":false,\"pairingType\":\"%s\",%s%s%s\"manifest\":%s}}", pin, pin ? "PIN" : "PROMPT", key[0] && !pin ? "\"client-key\":\"" : "", key[0] && !pin ? key : "", key[0] && !pin ? "\"," : "", MANIFEST);
    int ok = ws_text(c, reg); free(reg); if (!ok) { snprintf(err, ecap, "%s", T("The TV did not answer")); return 0; } }
  int registered = 0; double end = now_s() + 120;
  while (!registered && now_s() < end) {
    if (pin && ssapPinSet) { char pm[200]; pthread_mutex_lock(&mu); snprintf(pm, sizeof pm, "{\"type\":\"request\",\"id\":\"pin1\",\"uri\":\"ssap://pairing/setPin\",\"payload\":{\"pin\":\"%s\"}}", ssapPin); ssapPinSet = 0; pthread_mutex_unlock(&mu); ws_text(c, pm); set_state(i, S_CONNECTING, NULL); }
    char *r = ws_next(c, 500, m, sizeof m, &dead); if (dead) break; if (!r) continue; cJSON *js = cJSON_Parse(r); if (!js) continue;
    const char *ty = js_str(js, "type", ""); const cJSON *pl = js_obj(js, "payload");
    if (!strcmp(ty, "registered")) { const char *ck = js_str(pl, "client-key", ""); if (*ck) { pthread_mutex_lock(&mu); snprintf(newKey, sizeof newKey, "%s", ck); snprintf(newKeyIp, sizeof newKeyIp, "%s", ip); pthread_mutex_unlock(&mu); } registered = 1; }
    else if (!strcmp(ty, "response") && !strcmp(js_str(pl, "pairingType", ""), "PROMPT")) set_state(i, S_ALLOW, NULL);
    else if (!strcmp(ty, "response") && !strcmp(js_str(pl, "pairingType", ""), "PIN")) { ssapPinWait = 1; set_state(i, S_PIN, NULL); }
    else if (!strcmp(ty, "error") && !strcmp(js_str(js, "id", ""), "pin1")) { ssapPinWait = 1; set_state(i, S_PIN, T("Wrong PIN, try again")); }
    else if (!strcmp(ty, "error") && !pin && key[0]) { cJSON_Delete(js); key[0] = 0; goto regAgain; } /* (its key forgotten by the TV: asked again) */
    else if (!strcmp(ty, "error") && !pin) { cJSON_Delete(js); pin = 1; goto regAgain; } /* (no on-screen prompt on this TV: its PIN) */
    else if (!strcmp(ty, "error")) { snprintf(err, ecap, "%s", T("The TV said no to this phone")); cJSON_Delete(js); ssapPinWait = 0; return 0; }
    cJSON_Delete(js); }
  ssapPinWait = 0;
  if (!registered) { snprintf(err, ecap, "%s", T("Not allowed on the TV")); return 0; }
  set_state(i, S_OPENING, NULL);
  ws_text(c, "{\"type\":\"request\",\"id\":\"info1\",\"uri\":\"ssap://com.webos.service.connectionmanager/getinfo\"}"); /* (how to wake it later) */
  ws_text(c, "{\"type\":\"request\",\"id\":\"launch1\",\"uri\":\"ssap://system.launcher/launch\",\"payload\":{\"id\":\"" TV_APP_LG "\",\"params\":{\"cast\":1}}}"); /* (opened for a phone: the TV holds its background trailer until the phone's play comes) */
  end = now_s() + 15; int done = 0, ok = 0;
  while (!done && now_s() < end) { char *r = ws_next(c, 1000, m, sizeof m, &dead); if (dead) break; if (!r) continue; cJSON *js = cJSON_Parse(r); if (!js) continue; const char *id = js_str(js, "id", ""); const cJSON *pl = js_obj(js, "payload");
    if (!strcmp(id, "info1")) { const char *mac = js_str(js_obj(pl, "wiredInfo"), "macAddress", ""); if (!*mac || strcmp(js_str(js_obj(pl, "wiredInfo"), "state", ""), "connected")) { const char *w = js_str(js_obj(pl, "wifiInfo"), "macAddress", ""); if (*w) mac = w; }
      if (*mac) { pthread_mutex_lock(&mu); snprintf(newMac, sizeof newMac, "%s", mac); snprintf(newMacIp, sizeof newMacIp, "%s", ip); pthread_mutex_unlock(&mu); } }
    else if (!strcmp(id, "launch1")) { done = 1; if (!strcmp(js_str(js, "type", ""), "error") || !js_bool(pl, "returnValue", 1)) { const char *e = js_str(js, "error", js_str(pl, "errorText", "")); snprintf(err, ecap, "%s", strstr(e, "not found") || strstr(e, "404") || strstr(e, "exist") ? T("Stremio Origin is not on this TV") : T("The TV would not open the app")); } else ok = 1; }
    cJSON_Delete(js); }
  if (!done) snprintf(err, ecap, "%s", T("The TV did not answer"));
  return ok; }
/* Wake-on-LAN: six 0xFF, then the TV's address sixteen times, to the whole network (the TV listens for it while off
   when "Turn on via Wi-Fi" / "Mobile TV On" is allowed in its settings) */
static void wol(const char *mac, const char *ip) { unsigned mm[6]; if (sscanf(mac, "%x:%x:%x:%x:%x:%x", &mm[0], &mm[1], &mm[2], &mm[3], &mm[4], &mm[5]) != 6) return;
  unsigned char pk[102]; memset(pk, 0xff, 6); for (int i = 0; i < 16; i++) for (int k = 0; k < 6; k++) pk[6 + i * 6 + k] = (unsigned char)mm[k];
  int fd = socket(AF_INET, SOCK_DGRAM, 0); if (fd < 0) return; int on = 1; setsockopt(fd, SOL_SOCKET, SO_BROADCAST, &on, sizeof on);
  char bc[48]; snprintf(bc, sizeof bc, "%s", ip); char *dot = strrchr(bc, '.'); if (dot) snprintf(dot + 1, 4, "255");
  const char *to[3] = { "255.255.255.255", bc, ip }; for (int i = 0; i < 3; i++) for (int port = 7; port <= 9; port += 2) { struct sockaddr_in a; memset(&a, 0, sizeof a); a.sin_family = AF_INET; a.sin_port = htons(port); inet_pton(AF_INET, to[i], &a.sin_addr); sendto(fd, pk, sizeof pk, 0, (struct sockaddr *)&a, sizeof a); }
  close(fd); }

/* ---- Samsung (Tizen): its own remote API. 8001: what it is (its Wi-Fi address, to wake it later) and opening an app
   by REST; else 8002 (wss, its own certificate): the TV asks once to allow this phone, then a token (kept with the TV,
   as LG's key), and the app opened through it. Off: woken over Wi-Fi ("Power On with Mobile") ---- */
static int sam_info(const char *ip, int ms) { char u[96]; snprintf(u, sizeof u, "http://%s:8001/api/v2/", ip); size_t len; int st; unsigned char *b = net_fetch_sync(u, &len, &st, ms); if (!b) return 0;
  cJSON *j = cJSON_Parse((char *)b); free(b); if (!j) return 0; const char *mac = js_str(js_obj(j, "device"), "wifiMac", "");
  if (*mac) { pthread_mutex_lock(&mu); snprintf(newMac, sizeof newMac, "%s", mac); snprintf(newMacIp, sizeof newMacIp, "%s", ip); pthread_mutex_unlock(&mu); } cJSON_Delete(j); return 1; }
static int sam_rest_open(const char *ip, const char *app) { CURL *c = curl_easy_init(); if (!c) return 0; char u[160]; snprintf(u, sizeof u, "http://%s:8001/api/v2/applications/%s", ip, app);
  curl_easy_setopt(c, CURLOPT_URL, u); curl_easy_setopt(c, CURLOPT_POST, 1L); curl_easy_setopt(c, CURLOPT_POSTFIELDS, ""); curl_easy_setopt(c, CURLOPT_TIMEOUT_MS, 4000L); curl_easy_setopt(c, CURLOPT_NOSIGNAL, 1L);
  long code = 0; int ok = curl_easy_perform(c) == CURLE_OK && (curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &code), code >= 200 && code < 300); curl_easy_cleanup(c); fprintf(stderr, "[cast] samsung: REST open %s: %ld\n", app, code); return ok; }
static int sam_ws_open(int i, const char *ip, const char *tok0, char *err, size_t ecap) {
  static const char b64[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"; const char *nm = "Stremio Origin"; char enc[64]; size_t n = strlen(nm), o = 0;
  for (size_t q = 0; q < n; q += 3) { unsigned v = (unsigned char)nm[q] << 16 | (q + 1 < n ? (unsigned char)nm[q + 1] << 8 : 0) | (q + 2 < n ? (unsigned char)nm[q + 2] : 0); enc[o++] = b64[v >> 18 & 63]; enc[o++] = b64[v >> 12 & 63]; enc[o++] = q + 1 < n ? b64[v >> 6 & 63] : '='; enc[o++] = q + 2 < n ? b64[v & 63] : '='; } enc[o] = 0;
  char u[400]; snprintf(u, sizeof u, "wss://%s:8002/api/v2/channels/samsung.remote.control?name=%s%s%s", ip, enc, tok0[0] ? "&token=" : "", tok0); CURL *c = ws_open(u, 3000); if (!c) { snprintf(err, ecap, "%s", T("The TV did not answer")); return 0; }
  char m[16384]; int dead, conn = 0; double end = now_s() + 60, askAt = now_s() + 1.5;
  while (!conn && now_s() < end) { if (now_s() > askAt) { askAt = end + 1; set_state(i, S_ALLOW, NULL); } /* (no answer at once: the TV is asking to allow this phone) */
    char *r = ws_next(c, 500, m, sizeof m, &dead); if (dead) break; if (!r) continue; cJSON *js = cJSON_Parse(r); if (!js) continue; const char *ev = js_str(js, "event", "");
    if (!strcmp(ev, "ms.channel.connect")) { const char *tk = js_str(js_obj(js, "data"), "token", ""); if (*tk) { pthread_mutex_lock(&mu); snprintf(newKey, sizeof newKey, "%s", tk); snprintf(newKeyIp, sizeof newKeyIp, "%s", ip); newKeySam = 1; pthread_mutex_unlock(&mu); } conn = 1; }
    else if (!strcmp(ev, "ms.channel.unauthorized")) { cJSON_Delete(js); curl_easy_cleanup(c); snprintf(err, ecap, "%s", T("Not allowed on the TV")); return 0; }
    cJSON_Delete(js); }
  if (!conn) { curl_easy_cleanup(c); snprintf(err, ecap, "%s", T("Not allowed on the TV")); return 0; }
  set_state(i, S_OPENING, NULL); const char *ids[2] = { TV_APP_SAMSUNG, "StrOrigTV1" };
  for (int q = 0; q < 2; q++) { char cmd2[300]; snprintf(cmd2, sizeof cmd2, "{\"method\":\"ms.channel.emit\",\"params\":{\"event\":\"ed.apps.launch\",\"to\":\"host\",\"data\":{\"appId\":\"%s\",\"action_type\":\"NATIVE_LAUNCH\"}}}", ids[q]); ws_text(c, cmd2);
    double e2 = now_s() + 4; int bad = 0, good = 0; while (now_s() < e2 && !bad && !good) { char *r = ws_next(c, 500, m, sizeof m, &dead); if (dead) break; if (!r) continue; cJSON *js = cJSON_Parse(r); if (!js) continue; const char *ev = js_str(js, "event", "");
      if (!strcmp(ev, "ed.apps.launch")) { int code = (int)js_num(js, "data", 200); const cJSON *d = cJSON_GetObjectItemCaseSensitive(js, "data"); if (cJSON_IsNumber(d)) code = d->valueint; if (code == 200) good = 1; else bad = 1; } cJSON_Delete(js); }
    fprintf(stderr, "[cast] samsung: ws open %s: %s\n", ids[q], good ? "ok" : bad ? "refused" : "no answer"); if (good || !bad) { curl_easy_cleanup(c); return 1; } } /* (no answer is not a no: its app may still be starting) */
  curl_easy_cleanup(c); snprintf(err, ecap, "%s", T("Stremio Origin is not on this TV")); return 0; }
/* ---- one tap on a TV: our app answers -> connect; else LG reachable -> open the app -> connect; else wake it ->
   open the app -> connect. Each step one short line on its card ---- */
typedef struct { int i; char ip[48], key[128], mac[24]; int kind; } Job;
static Rx flowRx; static int flowRxSet, flowFor = -1; /* the app found: the main thread connects */
static void *flow_thread(void *a) { Job *j = a; Rx r; char err[160] = "";
  set_state(j->i, S_CONNECTING, NULL);
  if (rx_probe(j->ip, 900, &r)) goto found;
  if (j->kind == K_LG) {
    CURL *c = lg_open(j->ip, 2500);
    if (!c && j->mac[0]) { set_state(j->i, S_WAKING, NULL); pplat_multicast(1); double end = now_s() + 30, nextW = 0;
      while (now_s() < end && !c) { if (now_s() > nextW) { for (int k = 0; k < 3; k++) { wol(j->mac, j->ip); usleep(330000); } nextW = now_s() + 4; } /* 3 over 1 s, again every few seconds */
        if (rx_probe(j->ip, 600, &r)) { pplat_multicast(0); goto found; } c = lg_open(j->ip, 1200); }
      pplat_multicast(0);
      if (!c) { set_state(j->i, S_OFF, T("Did not wake: on the TV allow \xe2\x80\x9cTurn on via Wi-Fi\xe2\x80\x9d")); goto out; } }
    if (!c) { set_state(j->i, S_FAIL, T("Not answering. Is it on?")); goto out; }
    set_state(j->i, S_OPENING, NULL); int ok = lg_launch(j->i, c, j->ip, j->key, err, sizeof err); curl_easy_cleanup(c);
    if (!ok) { set_state(j->i, S_FAIL, err); goto out; }
    set_state(j->i, S_OPENING, NULL); double end = now_s() + 20; /* the app starting: until it answers */
    while (now_s() < end) if (rx_probe(j->ip, 1000, &r)) goto found;
    set_state(j->i, S_FAIL, T("The app opened but did not answer")); goto out; }
  if (j->kind == K_SAMSUNG) { /* Samsung: its remote API answers when it is on; off, woken over Wi-Fi first */
    int on = sam_info(j->ip, 2000);
    if (!on && j->mac[0]) { set_state(j->i, S_WAKING, NULL); pplat_multicast(1); double end = now_s() + 30, nextW = 0;
      while (now_s() < end && !on) { if (now_s() > nextW) { for (int k = 0; k < 3; k++) { wol(j->mac, j->ip); usleep(330000); } nextW = now_s() + 4; } if (rx_probe(j->ip, 600, &r)) { pplat_multicast(0); goto found; } on = sam_info(j->ip, 1200); }
      pplat_multicast(0); if (!on) { set_state(j->i, S_OFF, T("Did not wake: on the TV allow \xe2\x80\x9cPower On with Mobile\xe2\x80\x9d")); goto out; } }
    if (!on) { set_state(j->i, S_FAIL, T("Not answering. Is it on?")); goto out; }
    set_state(j->i, S_OPENING, NULL);
    int ok = sam_rest_open(j->ip, TV_APP_SAMSUNG) || sam_rest_open(j->ip, "StrOrigTV1"); if (!ok) ok = sam_ws_open(j->i, j->ip, j->key, err, sizeof err);
    if (!ok) { set_state(j->i, S_FAIL, err); goto out; }
    set_state(j->i, S_OPENING, NULL); double end = now_s() + 25; /* the app starting (a cold start takes longer): until it answers */
    while (now_s() < end) if (rx_probe(j->ip, 1000, &r)) goto found;
    set_state(j->i, S_FAIL, T("The app opened but did not answer")); goto out; }
  if (j->kind == K_ANDROID) { /* Google's TV remote on the box: wake it if needed, open our app; paired once with the code it shows */
    set_state(j->i, S_OPENING, NULL); int rc = pplat_atv_open(j->ip, "stremioorigin://open?cast=1");
    if (rc < 0 && j->mac[0]) { set_state(j->i, S_WAKING, NULL); pplat_multicast(1); double end = now_s() + 25, nextW = 0; /* asleep off the network: woken over Wi-Fi first */
      while (now_s() < end && rc < 0) { if (now_s() > nextW) { for (int k = 0; k < 3; k++) { wol(j->mac, j->ip); usleep(330000); } nextW = now_s() + 4; } if (rx_probe(j->ip, 600, &r)) { pplat_multicast(0); goto found; } rc = pplat_atv_open(j->ip, "stremioorigin://open?cast=1"); }
      pplat_multicast(0); }
    if (rc == 1) { /* this phone not known to it yet: the TV shows a code */
      if (pplat_atv_pair_start(j->ip, "Stremio Origin") != 0) { set_state(j->i, S_FAIL, T("Open Stremio Origin on this TV first")); goto out; }
      pthread_mutex_lock(&mu); atvCode[0] = 0; atvCodeSet = 0; atvWrong = 0; atvCodeWait = 1; pthread_mutex_unlock(&mu); set_state(j->i, S_PIN, NULL);
      double end = now_s() + 120; int done = 0;
      while (now_s() < end && !done) { usleep(100000); pthread_mutex_lock(&mu); int go = atvCodeSet, still = atvCodeWait; char code[8]; snprintf(code, sizeof code, "%s", atvCode); pthread_mutex_unlock(&mu);
        if (!still) break; if (!go) continue;
        int pr = pplat_atv_pair_finish(code);
        pthread_mutex_lock(&mu); atvCodeSet = 0; if (pr == 1) { atvWrong++; atvCode[0] = 0; } pthread_mutex_unlock(&mu);
        if (pr == 0) done = 1; else if (pr < 0) break; }
      pthread_mutex_lock(&mu); atvCodeWait = 0; pthread_mutex_unlock(&mu); pplat_atv_pair_close();
      if (!done) { set_state(j->i, S_FAIL, T("Not paired")); goto out; }
      set_state(j->i, S_OPENING, NULL); rc = pplat_atv_open(j->ip, "stremioorigin://open?cast=1"); }
    if (rc != 0) { set_state(j->i, S_FAIL, T("Open Stremio Origin on this TV first")); goto out; }
    double end = now_s() + 20; /* the app starting: until it answers */
    while (now_s() < end) if (rx_probe(j->ip, 1000, &r)) goto found;
    set_state(j->i, S_FAIL, T("Install Stremio Origin on this TV")); goto out; }
  set_state(j->i, S_FAIL, T("Stremio Origin is not open on this TV")); goto out;
found:
  set_state(j->i, S_CONNECTING, NULL); pthread_mutex_lock(&mu); flowRx = r; flowRxSet = 1; flowFor = j->i; pthread_mutex_unlock(&mu);
out:
  pthread_mutex_lock(&mu); flowBusy = 0; pthread_mutex_unlock(&mu); free(j); return NULL; }
static void connect_tv(int i) {
  pthread_mutex_lock(&mu); if (flowBusy || i < 0 || i >= ntv) { pthread_mutex_unlock(&mu); return; } flowBusy = 1; Job *j = calloc(1, sizeof *j); j->i = i; j->kind = tvs[i].kind; snprintf(j->ip, sizeof j->ip, "%s", tvs[i].ip); snprintf(j->mac, sizeof j->mac, "%s", tvs[i].mac); pthread_mutex_unlock(&mu);
  { char kn[80]; snprintf(kn, sizeof kn, j->kind == K_SAMSUNG ? "samtok_%s" : "lgkey_%s", j->ip); snprintf(j->key, sizeof j->key, "%s", store_get(kn, "")); }
  chosen = i; pthread_t th; if (pthread_create(&th, NULL, flow_thread, j) == 0) pthread_detach(th); else { free(j); flowBusy = 0; } }

/* ---- playing on the TV ---- */
static char *pendingPlay; /* a stream chosen before the TV was connected: sent once it is */
static char castType[16], castId[96], castVid[96]; /* what was last sent to the TV (its artwork on the remote) */
static void play_json(const Stream *s, const char *type, const char *id, const char *vid, double startSec, char **out) {
  const cJSON *mt = sb_meta_cached(type, id); int se = 0, ep = 0; const char *c = vid ? strchr(vid, ':') : NULL; if (c) sscanf(c, ":%d:%d", &se, &ep);
  char title[300]; if (se || ep) snprintf(title, sizeof title, "%s  S%d E%d", js_str(mt, "name", ""), se, ep); else snprintf(title, sizeof title, "%s", js_str(mt, "name", ""));
  cJSON *o = cJSON_CreateObject(); cJSON_AddStringToObject(o, "t", "play"); cJSON_AddStringToObject(o, "url", s->url); cJSON_AddStringToObject(o, "title", title); cJSON_AddNumberToObject(o, "pos", startSec > 0 ? startSec : 0);
  cJSON_AddItemToObject(o, "subs", cJSON_CreateArray());
  cJSON *m = cJSON_AddObjectToObject(o, "meta"); cJSON_AddStringToObject(m, "type", !strcmp(type, "series") ? "series" : live_type(type) ? type : "movie"); cJSON_AddStringToObject(m, "id", id); { const char *k3[3] = { "poster", "background", "logo" }; for (int q = 0; q < 3; q++) { const char *u = js_str(mt, k3[q], ""); if (*u) cJSON_AddStringToObject(m, k3[q], u); } } /* (its artwork: the TV shows it while it loads) */ if (se || ep) { cJSON_AddNumberToObject(m, "season", se); cJSON_AddNumberToObject(m, "episode", ep); }
  *out = cJSON_PrintUnformatted(o); cJSON_Delete(o); }
static void rm_open(void);
/* a channel started on the phone while casting: handed to the TV as a channel (it finds its stream, its channel player) */
static void rm_open(void);
static void cast_live(const Item *it) {
  cJSON *o = cJSON_CreateObject(); cJSON_AddStringToObject(o, "t", "play"); cJSON_AddStringToObject(o, "url", ""); cJSON_AddStringToObject(o, "title", it->name); cJSON_AddNumberToObject(o, "pos", 0); cJSON_AddItemToObject(o, "subs", cJSON_CreateArray());
  cJSON *m = cJSON_AddObjectToObject(o, "meta"); cJSON_AddStringToObject(m, "type", it->type[0] ? it->type : "tv"); cJSON_AddStringToObject(m, "id", it->id); if (it->poster[0]) cJSON_AddStringToObject(m, "poster", it->poster); if (it->logo[0]) cJSON_AddStringToObject(m, "logo", it->logo);
  char *js = cJSON_PrintUnformatted(o); cJSON_Delete(o); if (!js) return;
  snprintf(castType, sizeof castType, "%s", it->type[0] ? it->type : "tv"); snprintf(castId, sizeof castId, "%s", it->id); snprintf(castVid, sizeof castVid, "%s", it->id);
  if (cast_connected()) { cx_send(js); free(js); pthread_mutex_lock(&mu); snprintf(CX.ts, sizeof CX.ts, "loading"); snprintf(CX.title, sizeof CX.title, "%s", it->name); pthread_mutex_unlock(&mu); rm_open(); } else free(js); }
int cast_play(const Stream *s, const char *type, const char *id, const char *vid, double startSec) {
  if (startSec < 0) { const cJSON *st = js_obj(lib_get(id), "state"); double to = js_num(st, "timeOffset", 0) / 1000.0, d = js_num(st, "duration", 0) / 1000.0; const char *v = js_str(st, "video_id", "");
    startSec = (to >= 30 && !(d > 0 && to > d * 0.96) && (!*v || !strcmp(v, vid))) ? to : 0; }
  char *js = NULL; play_json(s, type, id, vid, startSec, &js); if (!js) return 0; snprintf(castType, sizeof castType, "%s", type); snprintf(castId, sizeof castId, "%s", id); snprintf(castVid, sizeof castVid, "%s", vid ? vid : id);
  if (cast_connected()) { cx_send(js); free(js); pthread_mutex_lock(&mu); CX.ts[0] = 0; snprintf(CX.ts, sizeof CX.ts, "loading"); pthread_mutex_unlock(&mu); rm_open(); return 1; }
  free(pendingPlay); pendingPlay = js; cast_open(); return 1; }
int cast_connected(void) { pthread_mutex_lock(&mu); int on = CX.st == CX_READY; pthread_mutex_unlock(&mu); return on; }
const char *cast_tv_name(void) { static char n[96]; pthread_mutex_lock(&mu); snprintf(n, sizeof n, "%s", CX.name); pthread_mutex_unlock(&mu); return n; }
/* the cast button: 0 no TV seen (dim), 1 a TV seen or remembered, 2 connecting (it pulses), 3 connected (it glows) */
int cast_icon_state(void) { pthread_mutex_lock(&mu); int seen = 0; for (int i = 0; i < ntv; i++) seen += tv_here(i); int s = CX.st == CX_READY ? 3 : (CX.st == CX_CONNECTING || CX.st == CX_PAIR || flowBusy) ? 2 : seen > 0 ? 1 : 0; pthread_mutex_unlock(&mu); return s; }
static void cmd(const char *s) { if (cast_connected()) cx_send(s); }
static void play_want(int play) { pthread_mutex_lock(&mu); int pw = CX.pw; pthread_mutex_unlock(&mu); if (play && pw >= 0) { cmd("{\"t\":\"playnow\"}"); fprintf(stderr, "[cast] play now (the previews' wait skipped)\n"); return; } /* (the TV waiting for the seek previews: Play starts the film now) */
  fprintf(stderr, "[cast] %s\n", play ? "resume" : "pause"); cmd(play ? "{\"t\":\"resume\"}" : "{\"t\":\"pause\"}"); pthread_mutex_lock(&mu); snprintf(wantTs, sizeof wantTs, "%s", play ? "playing" : "paused"); wantAt = now_s(); if (!strcmp(CX.ts, "playing") || !strcmp(CX.ts, "paused")) { if (!play && !strcmp(CX.ts, "playing") && CX.posAt > 0) { CX.pos += now_s() - CX.posAt; CX.posAt = now_s(); } snprintf(CX.ts, sizeof CX.ts, "%s", wantTs); } pthread_mutex_unlock(&mu); notifyNow = 1; }
static void rm_jump(int d, int b); static Tween jbA; static int jbDir, jbN; static double jbAt; /* the last jump: its button, how many in a row, when */
/* the TV follows the phone: its account (signed out or someone else's there: signed in as this one) and its playback
   settings; sent once connected and again whenever they change */
static const char *PREFS[] = { "autoBest", "subsLang", "defaultAudioTrack", "enableDefaultAudioTrack", "subtitleSize", "subsColor", "subsBgStyle", "subsOutlineColor", "subsAssStyle", "subsPosPct", "enableNextVideo", "bingeWatch", "seekStep", "aspectMode", "bgTrailer", "bgTrailerVol", "uiSound", "uiSoundVol", "accent", "ssDelay", "uiLang", "subsFont", "subsFontAr", "subsBright", "seekPreviews", "subsMode" }; /* (all the TV follows: sent on every connection, again on any change) */
static char *follow_json(int which) { cJSON *o = cJSON_CreateObject();
  if (!which) { cJSON_AddStringToObject(o, "t", "account"); const char *ak = sb_auth_key(); cJSON_AddStringToObject(o, "authKey", ak ? ak : ""); const cJSON *u = store_node("user"); cJSON_AddItemToObject(o, "user", u ? cJSON_Duplicate(u, 1) : cJSON_CreateObject()); }
  else { cJSON_AddStringToObject(o, "t", "settings"); cJSON *p = cJSON_AddObjectToObject(o, "prefs"); for (size_t i = 0; i < sizeof PREFS / sizeof *PREFS; i++) { const char *v = store_get(PREFS[i], NULL); if (v) cJSON_AddStringToObject(p, PREFS[i], v); } }
  char *s = cJSON_PrintUnformatted(o); cJSON_Delete(o); return s; }
static void follow_tick(int justReady) { static unsigned lastA, lastS; static double at; if (!cast_connected()) { lastA = lastS = 0; return; } if (!justReady && now_s() - at < 2) return; at = now_s();
  for (int w = 0; w < 2; w++) { char *s = follow_json(w); if (!s) continue; unsigned h = 2166136261u; for (const char *c = s; *c; c++) h = (h ^ (unsigned char)*c) * 16777619u; unsigned *last = w ? &lastS : &lastA; if (h != *last) { *last = h; cx_send(s); } free(s); } }
/* best stream on: found by the TV itself, for what it can play (its codecs, HDR, its addons as it has them); a TV that
   cannot yet: chosen on the phone and sent (its remote shows it being found either way) */
static unsigned cbTok;
static void cb_done(const Stream *st, const BestRate *r, void *ud) { (void)r; if ((unsigned)(uintptr_t)ud != cbTok) return;
  if (!st) { pthread_mutex_lock(&mu); snprintf(CX.ts, sizeof CX.ts, "error"); pthread_mutex_unlock(&mu); toast(T("No stream suits this title. Pick one from the list"), 2600, NULL); return; }
  Stream s2 = *st; cast_play(&s2, castType, castId, castVid, -1); }
static void cb_status(const char *t, void *ud) { (void)t; (void)ud; }
void cast_choose_best(const char *type, const char *id, const char *vid) {
  snprintf(castType, sizeof castType, "%s", type); snprintf(castId, sizeof castId, "%s", id); snprintf(castVid, sizeof castVid, "%s", vid ? vid : id);
  pthread_mutex_lock(&mu); snprintf(CX.ts, sizeof CX.ts, "choosing"); CX.title[0] = 0; CX.pos = CX.dur = 0; pthread_mutex_unlock(&mu);
  pthread_mutex_lock(&mu); int tvBest = CX.st == CX_READY && CX.tvBest; pthread_mutex_unlock(&mu);
  if (tvBest) { const cJSON *mt = sb_meta_cached(type, id); int se = 0, ep = 0; const char *c = strchr(castVid, ':'); if (c) sscanf(c, ":%d:%d", &se, &ep);
    const cJSON *st = js_obj(lib_get(id), "state"); double to = js_num(st, "timeOffset", 0) / 1000.0, d = js_num(st, "duration", 0) / 1000.0; const char *v = js_str(st, "video_id", ""); double at = (to >= 30 && !(d > 0 && to > d * 0.96) && (!*v || !strcmp(v, castVid))) ? to : 0;
    char title[300]; if (se || ep) snprintf(title, sizeof title, "%s  S%d E%d", js_str(mt, "name", ""), se, ep); else snprintf(title, sizeof title, "%s", js_str(mt, "name", ""));
    cJSON *o = cJSON_CreateObject(); cJSON_AddStringToObject(o, "t", "playbest"); cJSON_AddStringToObject(o, "title", title); cJSON_AddNumberToObject(o, "pos", at);
    cJSON *m = cJSON_AddObjectToObject(o, "meta"); cJSON_AddStringToObject(m, "type", !strcmp(type, "series") ? "series" : "movie"); cJSON_AddStringToObject(m, "id", id); cJSON_AddStringToObject(m, "vid", castVid);
    { const char *k3[3] = { "poster", "background", "logo" }; for (int q = 0; q < 3; q++) { const char *u = js_str(mt, k3[q], ""); if (*u) cJSON_AddStringToObject(m, k3[q], u); } } if (se || ep) { cJSON_AddNumberToObject(m, "season", se); cJSON_AddNumberToObject(m, "episode", ep); }
    char *js = cJSON_PrintUnformatted(o); cJSON_Delete(o); if (js) { cx_send(js); free(js); } rm_open(); return; }
  int dur = strcmp(type, "series") ? 100 : 45; best_choose(type, castVid, dur, cb_status, cb_done, (void *)(uintptr_t)++cbTok); rm_open(); }

void cast_pump(void) {
  { char e[200] = ""; pthread_mutex_lock(&mu); if (chErr[0]) { snprintf(e, sizeof e, "%s", chErr); chErr[0] = 0; } pthread_mutex_unlock(&mu); if (e[0]) toast(e, 2800, LIVE_TOAST); }
  { static unsigned seen; pthread_mutex_lock(&mu); if (CX.pgen != seen) { seen = CX.pgen; snprintf(castType, sizeof castType, "%s", CX.ptype); snprintf(castId, sizeof castId, "%s", CX.pid); snprintf(castVid, sizeof castVid, "%s", CX.pvid[0] ? CX.pvid : CX.pid); } pthread_mutex_unlock(&mu); } /* (what the TV plays now: the remote's picture and the notification follow it) */
  static int lastSt = -1; static double scannedAt;
  if (!scannedAt || now_s() - scannedAt > (shOpen ? 20 : 45)) { scannedAt = now_s(); scan(); } /* (now and then: the button knows whether a TV is around; the sheet open, more often, so what it lists is what answers) */
  pthread_mutex_lock(&mu);
  if (newKey[0]) { char kn[80]; snprintf(kn, sizeof kn, newKeySam ? "samtok_%s" : "lgkey_%s", newKeyIp); pthread_mutex_unlock(&mu); store_set(kn, newKey); pthread_mutex_lock(&mu); newKey[0] = 0; }
  if (newMac[0]) { for (int k = 0; k < ntv; k++) if (!strcmp(tvs[k].ip, newMacIp)) snprintf(tvs[k].mac, sizeof tvs[k].mac, "%s", newMac); newMac[0] = 0; }
  int go = flowRxSet; Rx r = flowRx; int fi = flowFor; flowRxSet = 0;
  char tokNew[80], id[64]; snprintf(tokNew, sizeof tokNew, "%s", CX.tokNew); CX.tokNew[0] = 0; snprintf(id, sizeof id, "%s", CX.id); int tokBad = CX.tokBad; CX.tokBad = 0; int st = CX.st, ti = CX.tvIdx; char err[160]; snprintf(err, sizeof err, "%s", CX.err); CX.err[0] = 0; char name[96]; snprintf(name, sizeof name, "%s", CX.name);
  pthread_mutex_unlock(&mu);
  if (go) { if (fi >= 0 && fi < ntv) { pthread_mutex_lock(&mu); tvs[fi].origin = 1; snprintf(tvs[fi].id, sizeof tvs[fi].id, "%s", r.id); if (r.mac[0]) snprintf(tvs[fi].mac, sizeof tvs[fi].mac, "%s", r.mac); tvs[fi].port = r.port; pthread_mutex_unlock(&mu); } cx_start(fi, &r); }
  if (tokNew[0] && id[0]) { char k[96]; snprintf(k, sizeof k, "casttok_%s", id); store_set(k, tokNew); }
  if (tokBad && id[0]) { char k[96]; snprintf(k, sizeof k, "casttok_%s", id); store_set(k, ""); Rx rr; memset(&rr, 0, sizeof rr); pthread_mutex_lock(&mu); snprintf(rr.ip, sizeof rr.ip, "%s", CX.ip); snprintf(rr.id, sizeof rr.id, "%s", CX.id); rr.port = CX.port; pthread_mutex_unlock(&mu); cx_start(ti, &rr); } /* (its token no longer good: paired again) */
  linkIdx = st != CX_OFF ? ti : -1;
  /* the card follows the connection */
  if (ti >= 0 && ti < ntv) { int want = st == CX_READY ? S_ON : st == CX_PAIR ? S_PAIR : st == CX_CONNECTING ? S_CONNECTING : -1; pthread_mutex_lock(&mu); int cur = tvs[ti].state; pthread_mutex_unlock(&mu);
    if (want >= 0 && cur != want) set_state(ti, want, NULL); else if (want < 0 && (cur == S_ON || cur == S_PAIR || (cur == S_CONNECTING && !flowBusy))) set_state(ti, err[0] ? S_FAIL : S_IDLE, err); }
  follow_tick(st == CX_READY && lastSt != CX_READY);
  { void pplat_cast_notify(const char *title, const char *sub, const char *art, int playing, double pos, double dur); int pplat_cast_take(int *kind, double *val);
    int k; double v; while (pplat_cast_take(&k, &v)) { pthread_mutex_lock(&mu); int pl = !strcmp(CX.ts, "playing"); pthread_mutex_unlock(&mu); /* the notification's and the lock screen's presses */
      if (k >= 1 && k <= 7) fprintf(stderr, "[cast] from the notification or lock screen: %d\n", k); /* (which press sent it: a pause no one asked for shows where it came from) */ if (k == 1) play_want(!pl); else if (k == 5) play_want(1); else if (k == 6) play_want(0); else if (k == 4) cmd("{\"t\":\"stop\"}");
      else if (k == 2 || k == 3) rm_jump(k == 2 ? -10 : 10, 0); else if (k == 7) { char m2[80]; snprintf(m2, sizeof m2, "{\"t\":\"seek\",\"pos\":%.1f}", v); cmd(m2); } }
    static double nAt; static int nOn; pthread_mutex_lock(&mu); char ts2[16], ti2[200], nm2[96]; snprintf(ts2, sizeof ts2, "%s", CX.ts); snprintf(ti2, sizeof ti2, "%s", CX.title); snprintf(nm2, sizeof nm2, "%s", CX.name); double ps = CX.pos, du = CX.dur; pthread_mutex_unlock(&mu);
    int act = !strcmp(ts2, "playing") || !strcmp(ts2, "paused") || !strcmp(ts2, "loading") || !strcmp(ts2, "choosing"), show = st == CX_READY && act; /* only while something plays on the TV (what plays, its controls); connected with nothing playing: no notification */
    if (show && (now_s() - nAt > 1 || !nOn || notifyNow)) { notifyNow = 0; nAt = now_s(); nOn = 1; const cJSON *mt = act && castId[0] ? sb_meta_cached(castType, castId) : NULL; const char *art = js_str(mt, "background", js_str(mt, "poster", ""));
      if (act) pplat_cast_notify(ti2[0] ? ti2 : js_str(mt, "name", nm2), nm2, art, !strcmp(ts2, "playing"), ps, du); else pplat_cast_notify(nm2, "", "", 0, 0, 0); }
    else if (!show && nOn) { nOn = 0; pplat_cast_notify(NULL, NULL, NULL, 0, 0, 0); } }
  if (st != lastSt) {
    if (st == CX_READY) { pthread_mutex_lock(&mu); Tv keep; int ok = ti >= 0 && ti < ntv; if (ok) keep = tvs[ti]; pthread_mutex_unlock(&mu); if (ok) { snprintf(keep.name, sizeof keep.name, "%s", name); remember(&keep); }
      if (pendingPlay) { cx_send(pendingPlay); free(pendingPlay); pendingPlay = NULL; { extern int player_open(void); extern void player_back(void); if (player_open()) player_back(); } /* (sent from the player: it gives way to the TV) */ pthread_mutex_lock(&mu); snprintf(CX.ts, sizeof CX.ts, "loading"); pthread_mutex_unlock(&mu); if (shOpen) { shCloseAt = now_s() + 0.6; } rm_open(); }
      else if (shOpen) shCloseAt = now_s() + 0.9; pplat_haptic_k(HK_POP, 0.8f); }
    lastSt = st; }
}

/* the cast sheets' card: the bar's liquid glass over the page, darker for what is on it */
static int rmMorph; /* the remote pulled down while a title plays: it shrinks toward the mini player with the finger (its own glass drawn there) */
static float gsW = -1, gsX = 12, gsPW; /* the panel's width when it hugs what is on it (the remote sideways), else the whole sheet; where it was drawn */
static float glass_sheet(float h, float a) { float y = sheet_panel_bare(h, a), m = 12, ch = h - INS_B + 10, pw = gsW > 0 ? fminf(gsW, SB_W - 2 * m) : SB_W - 2 * m, px = (SB_W - pw) / 2; gsX = px; gsPW = pw; if (rmMorph) return y;
  extern void ph_glass_grab_liquid(void); extern void ph_liquid_bubble(float x, float y, float w, float h, float r, float press); ph_glass_grab_liquid();
  ph_liquid_bubble(px, y, pw, ch, 46, 0); gfx_rrect(px, y, pw, ch, 46, RGBA(14, 12, 20, 165)); gfx_ring(px, y, pw, ch, 46, 1, WHITE_A(30));
  gfx_rrect(SB_W / 2 - 34, y + 14, 68, 6, 3, WHITE_A(70)); return y; }
/* ---- the sheet: the TVs (cards in the app's own look, each line crossfading as it changes); pairing: the code ---- */
static void tv_act(int i, int b) { (void)b; pthread_mutex_lock(&mu); int st = i < ntv ? tvs[i].state : 0; pthread_mutex_unlock(&mu);
  if (st == S_CONNECTING || st == S_WAKING || st == S_OPENING || st == S_ALLOW || st == S_PAIR || st == S_PIN) return; /* (already on its way) */
  if (st == S_ON) { rm_open(); return; }
  pplat_haptic_k(HK_TICK, 0.6f); connect_tv(i); }
static void again_act(int a, int b) { (void)a; (void)b; pplat_haptic_k(HK_TICK, 0.5f); scan(); }
static void off_act(int a, int b) { (void)a; (void)b; pthread_mutex_lock(&mu); CX.stop = 1; CX.st = CX_OFF; int ti = CX.tvIdx; if (ti >= 0 && ti < ntv) { tvs[ti].state = S_IDLE; tvs[ti].stAt = now_s(); } pthread_mutex_unlock(&mu); chosen = -1; pplat_haptic_k(HK_TICK, 0.5f); if (rmOpen) ph_sheet_close(); }
/* one number pad: the TV's code (4 digits, sent at once), an LG TV's PIN (sent with OK), a TV's address (digits and dots) */
enum { PAD_CODE = 0, PAD_PIN, PAD_IP, PAD_HEX }; static int padIp; static char ipBuf[20];
static int pad_mode(void) { pthread_mutex_lock(&mu); int pairing = CX.st == CX_PAIR; pthread_mutex_unlock(&mu); return pairing ? PAD_CODE : atvCodeWait ? PAD_HEX : ssapPinWait ? PAD_PIN : padIp ? PAD_IP : -1; }
static void pad_add(int i);
static void digit_act(int d, int b) { (void)b; int md = pad_mode();
  if (md == PAD_HEX) { pthread_mutex_lock(&mu); size_t l = strlen(atvCode); if (d == -1) { if (l && !atvCodeSet) atvCode[l - 1] = 0; } else if (d >= 0 && d < 16 && l < 6 && !atvCodeSet) { atvCode[l] = "0123456789ABCDEF"[d]; atvCode[l + 1] = 0; if (l + 1 == 6) atvCodeSet = 1; } pthread_mutex_unlock(&mu); pplat_haptic_k(HK_TICK, 0.4f); return; } /* (the sixth: it goes) */
  pthread_mutex_lock(&mu);
  char *buf = md == PAD_CODE ? CX.code : md == PAD_PIN ? ssapPin : ipBuf; size_t cap = md == PAD_CODE ? 5 : md == PAD_PIN ? 9 : 16, l = strlen(buf);
  if (d == -1) { if (l) buf[l - 1] = 0; }
  else if (d == -3) { if (md == PAD_PIN && l) { ssapPinSet = 1; ssapPinWait = 0; } } /* (OK: the PIN goes) */
  else if (l + 1 < cap) { buf[l] = d == -4 ? '.' : (char)('0' + d); buf[l + 1] = 0; if (md == PAD_CODE && l + 1 == 4) CX.codeSet = 1; }
  pthread_mutex_unlock(&mu); pplat_haptic_k(HK_TICK, 0.4f);
  if (d == -3 && md == PAD_IP) pad_add(0); }
static void ip_open(int a, int b) { (void)a; (void)b; padIp = 1; ipBuf[0] = 0; }
static void ip_close(int a, int b) { (void)a; (void)b; padIp = 0; }
static void tv_add_ip(const char *ip) { struct in_addr t; if (inet_pton(AF_INET, ip, &t) != 1) { toast(T("That address is not right"), 1800, NULL); return; }
  pthread_mutex_lock(&mu); int j; for (j = 0; j < ntv; j++) if (!strcmp(tvs[j].ip, ip)) break;
  if (j == ntv && ntv < 16) { Tv *tv = &tvs[ntv++]; memset(tv, 0, sizeof *tv); snprintf(tv->ip, sizeof tv->ip, "%s", ip); snprintf(tv->name, sizeof tv->name, "%s", ip); tv->kind = K_LG; tv->stAt = now_s(); } /* (an LG is the one we can open the app on; our app answering is tried first anyway) */
  Tv keep = tvs[j < ntv ? j : ntv - 1]; pthread_mutex_unlock(&mu); remember(&keep); padIp = 0; connect_tv(j < ntv ? j : ntv - 1); }
static void pad_add(int i) { (void)i; char ip[20]; pthread_mutex_lock(&mu); snprintf(ip, sizeof ip, "%s", ipBuf); pthread_mutex_unlock(&mu); tv_add_ip(ip); }
static float pad_h(int md) { return md == PAD_HEX ? 92 + 108 + 80 + 5 * 100 : 92 + 108 + 80 + 4 * 100 + (md != PAD_CODE ? 110 : 0); }
/* an Android TV's pairing code: six characters, 0-9 and A-F, sent as the sixth is typed */
static void pad_hex_draw(float y, float cw) {
  pthread_mutex_lock(&mu); char code[8]; snprintf(code, sizeof code, "%s", atvCode); int sent = atvCodeSet, wrong = atvWrong; pthread_mutex_unlock(&mu);
  static int lastWrong; if (wrong != lastWrong) { lastWrong = wrong; if (wrong) pplat_haptic_k(HK_THUD, 1); }
  text_draw(T("Enter the code shown on the TV"), SB_W / 2, y, F_BODY, 700, TXT, 0, cw, ALIGN_CENTER);
  if (wrong && !code[0]) text_draw(T("Wrong code, try again"), SB_W / 2, y + 42, F_SMALL, 600, RGB(0xef, 0x8f, 0x8a), 0, cw, ALIGN_CENTER);
  float by = y + 92, bh = 108, gap = 12, bw = (cw - 5 * gap) / 6; if (bw > 92) bw = 92; float gx = SB_W / 2 - (6 * bw + 5 * gap) / 2;
  for (int k = 0; k < 6; k++) { float x = gx + k * (bw + gap); int has = (int)strlen(code) > k, cur = k == (int)strlen(code); gfx_rrect(x, by, bw, bh, 20, WHITE_A(has ? 22 : 10)); gfx_ring(x, by, bw, bh, 20, has || cur ? 2 : 1, has || cur ? col_alpha(ACC2, 0.8f) : WHITE_A(24));
    if (has) { char d[2] = { code[k], 0 }; text_draw(d, x + bw / 2, by + bh / 2 - text_line_height(F_H1) / 2.0f, F_H1, 800, TXT, 0, 0, ALIGN_CENTER); } }
  if (sent) spinner(SB_W / 2, by + bh + 40, 14);
  float ky = by + bh + 80, kw = (cw - 3 * 14) / 4, kh = 86; static const char *K = "123A456B789CD0EF";
  for (int q = 0; q < 17; q++) { int r = q / 4, c = q % 4; float x = PAD + c * (kw + 14), yy = ky + r * (kh + 14); if (q == 16) { x = PAD + 3 * (kw + 14); } int d = q == 16 ? -1 : (K[q] <= '9' ? K[q] - '0' : K[q] - 'A' + 10);
    int pr = ph_pressed(x, yy, kw, kh); gfx_rrect(x, yy, kw, kh, kh / 2, WHITE_A(pr ? 40 : 14));
    if (d >= 0) { char t2[2] = { K[q], 0 }; text_draw(t2, x + kw / 2, yy + kh / 2 - text_line_height(F_H2) / 2.0f, F_H2, 700, TXT, 0, 0, ALIGN_CENTER); } else icon_draw("ph_back", x + kw / 2 - 22, yy + kh / 2 - 22, 44, WHITE_A(220));
    hit_act(x, yy, kw, kh, digit_act, d, 0); } }
static void pad_draw(int md, float y, float cw) {
  pthread_mutex_lock(&mu); char code[20]; snprintf(code, sizeof code, "%s", md == PAD_CODE ? CX.code : md == PAD_PIN ? ssapPin : ipBuf); int locked = CX.locked, wrong = CX.wrong, sent = md == PAD_CODE && (CX.codeSet || strlen(CX.code) == 4); pthread_mutex_unlock(&mu);
  static int lastWrong; if (md == PAD_CODE && wrong != lastWrong) { lastWrong = wrong; pthread_mutex_lock(&mu); CX.code[0] = 0; pthread_mutex_unlock(&mu); code[0] = 0; sent = 0; pplat_haptic_k(HK_THUD, 1); }
  const char *ti = md == PAD_CODE ? T("Enter the code shown on the TV") : md == PAD_PIN ? T("Enter the PIN shown on the TV") : T("The TV\xe2\x80\x99s address");
  text_draw(ti, SB_W / 2, y, F_BODY, 700, TXT, 0, cw, ALIGN_CENTER);
  if (md == PAD_CODE && (locked || wrong)) text_draw(locked ? T("Too many tries: wait a minute, then refresh") : T("Wrong code, try again"), SB_W / 2, y + 42, F_SMALL, 600, RGB(0xef, 0x8f, 0x8a), 0, cw, ALIGN_CENTER);
  else if (md == PAD_IP) text_draw(T("On the TV: Settings, Network, Wi-Fi, Advanced"), SB_W / 2, y + 42, F_SMALL, 500, TXT3, 0, cw, ALIGN_CENTER);
  float by = y + 92, bh = 108;
  if (md == PAD_CODE) { float bw = 92, gx = SB_W / 2 - (4 * bw + 3 * 18) / 2; for (int k = 0; k < 4; k++) { float x = gx + k * (bw + 18); int has = (int)strlen(code) > k, cur = k == (int)strlen(code); gfx_rrect(x, by, bw, bh, 22, WHITE_A(has ? 22 : 10)); gfx_ring(x, by, bw, bh, 22, has || cur ? 2 : 1, has || cur ? col_alpha(ACC2, 0.8f) : WHITE_A(24));
      if (has) { char d[2] = { code[k], 0 }; text_draw(d, x + bw / 2, by + bh / 2 - text_line_height(F_H1) / 2.0f, F_H1, 800, TXT, 0, 0, ALIGN_CENTER); } } }
  else { gfx_rrect(PAD, by, cw, bh, 26, WHITE_A(12)); gfx_ring(PAD, by, cw, bh, 26, 2, col_alpha(ACC2, 0.7f)); float tw = text_draw(code, SB_W / 2, by + bh / 2 - text_line_height(F_H1) / 2.0f, F_H1, 800, TXT, 2, cw - 40, ALIGN_CENTER);
    if (fmod(now_s(), 1.0) < 0.55) gfx_rect(SB_W / 2 + tw / 2 + 4, by + 30, 3, bh - 60, ACC2); }
  if (sent) spinner(SB_W / 2, by + bh + 40, 14);
  float ky = by + bh + 80, kw = (cw - 2 * 16) / 3, kh = 86;
  for (int r = 0; r < 4; r++) for (int c = 0; c < 3; c++) { int d = r < 3 ? r * 3 + c + 1 : c == 1 ? 0 : c == 2 ? -1 : (md == PAD_IP ? -4 : -2); if (d == -2) continue; float x = PAD + c * (kw + 16), yy = ky + r * (kh + 14);
    int pr = ph_pressed(x, yy, kw, kh); gfx_rrect(x, yy, kw, kh, kh / 2, WHITE_A(pr ? 40 : 14));
    if (d >= 0) { char t2[2] = { (char)('0' + d), 0 }; text_draw(t2, x + kw / 2, yy + kh / 2 - text_line_height(F_H2) / 2.0f, F_H2, 700, TXT, 0, 0, ALIGN_CENTER); }
    else if (d == -4) text_draw(".", x + kw / 2, yy + kh / 2 - text_line_height(F_H1) / 2.0f, F_H1, 800, TXT, 0, 0, ALIGN_CENTER); else icon_draw("ph_back", x + kw / 2 - 22, yy + kh / 2 - 22, 44, WHITE_A(220));
    hit_act(x, yy, kw, kh, digit_act, d, 0); }
  if (md != PAD_CODE) { float oy = ky + 4 * (kh + 14) + 10, ow = md == PAD_IP ? (cw - 16) / 2 : cw; if (md == PAD_IP) button(PAD, oy, ow, 80, NULL, T("Cancel"), 0, ip_close, 0, 0); button(md == PAD_IP ? PAD + ow + 16 : PAD, oy, ow, 80, NULL, md == PAD_IP ? T("Add") : T("OK"), 1, digit_act, -3, 0); } }
static void sh_draw(float a) {
  if (shCloseAt > 0 && now_s() > shCloseAt) { shCloseAt = 0; ph_sheet_close(); }
  pthread_mutex_lock(&mu); Tv list[16]; int idx[16], n = 0, sc = scanning; for (int q = 0; q < ntv; q++) if (tv_here(q)) { list[n] = tvs[q]; idx[n++] = q; } pthread_mutex_unlock(&mu); int md = pad_mode(); /* (what answers now: never a list of the past) */
  static int lastMd = -1; static Tween padT; static float shH = -1; if (md >= 0) lastMd = md; tween_to(&padT, md >= 0 ? 1 : 0, 0.32f, EASE_WEB); tween_tick(&padT, phDt); float pk2 = padT.v; /* the address pad comes and goes softly: the sheet's height glides, one view fades into the other */
  float rowH = 92, gap = 10, cw = SB_W - 2 * PAD, hList = 140 + (n ? n * (rowH + gap) : 180) + 96 + INS_B, hPad = lastMd >= 0 ? 140 + pad_h(lastMd) + 40 + INS_B : hList, want = hList + (hPad - hList) * pk2;
  if (shH < 0 || a < 0.05f) shH = want; shH += (want - shH) * clampf(phDt * 14, 0, 1); float h = shH, y = glass_sheet(h, a);
  float in = ease_apply(EASE_OUT, clampf(a, 0, 1)); gfx_opacity_push(in);
  /* the head: the cast sign, its title, refresh; one line, centred on the same height */
  float hy = y + 70; text_draw(T("Cast to TV"), PAD, hy - text_line_height(F_H2 - 4) / 2.0f, F_H2 - 4, 800, TXT, -0.3f, cw - 90, ALIGN_START); /* its title, on the refresh's line */
  if (pk2 > 0.01f && lastMd >= 0) { gfx_opacity_push(pk2); gfx_offset_push(0, 24 * (1 - pk2)); if (lastMd == PAD_HEX) pad_hex_draw(y + 140, cw); else pad_draw(lastMd, y + 140, cw); gfx_offset_pop(); gfx_opacity_pop(); }
  if (md >= 0 && pk2 > 0.99f) { gfx_opacity_pop(); return; }
  if (pk2 < 0.99f) gfx_opacity_push(1 - pk2); else { gfx_opacity_pop(); return; }
  { float r = 30, cx = SB_W - PAD - r, cy = hy; int pr = ph_pressed(cx - r, cy - r, 2 * r, 2 * r); gfx_circle(cx, cy, r, WHITE_A(pr ? 40 : 16));
    { static float ang; static Tween spT; tween_to(&spT, sc ? 1 : 0, 0.3f, EASE_WEB); tween_tick(&spT, phDt); ang += phDt * 300 * spT.v; if (spT.v < 0.01f) ang = 0; else if (!sc && fmodf(ang, 360) > 350) ang = 0; /* looking: the button itself turns (no other loader), easing in and out */
      icon_draw_rot("st_sync", cx - 16, cy - 16, 32, WHITE_A(210), sc || spT.v > 0.01f ? ang : 0); } if (md < 0) hit_act(cx - r - 10, cy - r - 10, 2 * r + 20, 2 * r + 20, again_act, 0, 0); }
  float ry = y + 132;
  if (!n) { float cy = ry + 70; static Tween br; tween_to(&br, sc ? 1 : 0, 0.4f, EASE_WEB); tween_tick(&br, phDt); float pulse = 0.5f + 0.5f * sinf((float)now_s() * 2.4f), al = 60 + (int)(br.v * 110 * pulse); /* looking: the TV breathes in and out, slowly */
    icon_draw("ph_tv", SB_W / 2 - 32, cy - 32, 64, WHITE_A((int)al)); }
  for (int i = 0; i < n; i++, ry += rowH + gap) { Tv *t = &list[i]; int on = t->state == S_ON, off = t->state == S_OFF, fail = t->state == S_FAIL, busy2 = t->state == S_CONNECTING || t->state == S_WAKING || t->state == S_OPENING || t->state == S_ALLOW || t->state == S_PAIR || t->state == S_PIN;
    float rx = PAD, rw = cw, rr = 26, pk = press_k(rx, ry, rw, rowH), sk = 1 - 0.02f * pk; gfx_scale_push(sk, sk, rx + rw / 2, ry + rowH / 2); /* a TV: a slim card, its sign in a disc, its name and make, what it is doing on the right */
    static Tween lit[16]; tween_to(&lit[i], on ? 1 : 0, 0.3f, EASE_WEB); tween_tick(&lit[i], phDt); float lk = lit[i].v; /* (connected: it lights, smoothly) */
    gfx_rrect(rx, ry, rw, rowH, rr, col_mix(WHITE_A(off ? 6 : 10 + (int)(16 * pk)), WHITE_A(24), lk)); gfx_ring(rx, ry, rw, rowH, rr, 1, col_mix(WHITE_A(18), WHITE_A(60), lk));
    float dc = 52, dx = rx + 18, dcy = ry + rowH / 2; gfx_circle(dx + dc / 2, dcy, dc / 2, col_mix(WHITE_A(12), WHITE_A(235), lk)); icon_draw(on ? "ph_cast_on" : "ph_tv", dx + dc / 2 - 14, dcy - 14, 28, col_mix(WHITE_A(off ? 110 : 230), RGB(14, 12, 20), lk));
    const char *mk = t->kind == K_LG ? "LG" : t->kind == K_SAMSUNG ? "Samsung" : t->kind == K_ANDROID ? "Android TV" : "";
    float tx = dx + dc + 16, tw = rw - (tx - rx) - (on ? 170 : 64), l1 = text_line_height(F_BODY - 2), l2 = mk[0] ? text_line_height(F_TINY) + 2 : 0, ty = dcy - (l1 + l2) / 2;
    text_draw(t->name, tx, ty, F_BODY - 2, 700, off ? TXT2 : TXT, 0, tw, ALIGN_START); if (mk[0]) text_draw(mk, tx, ty + l1 + 2, F_TINY, 600, TXT3, 0, tw, ALIGN_START);
    gfx_scale_pop();
    if (busy2) spinner(rx + rw - 36, dcy, 12); else if (fail) gfx_circle(rx + rw - 36, dcy, 5, RGB(0xef, 0x8f, 0x8a));
    if (on) { const char *dl = T("Disconnect"); float pw = text_width(dl, F_TINY + 1, 700, 0) + 32, ph = 44, px = rx + rw - 18 - pw, py = dcy - ph / 2; gfx_rrect(px, py, pw, ph, ph / 2, WHITE_A(ph_pressed(px, py, pw, ph) ? 40 : 16));
      text_draw(dl, px + pw / 2, py + ph / 2 - text_line_height(F_TINY + 1) / 2.0f, F_TINY + 1, 700, WHITE_A(225), 0, 0, ALIGN_CENTER); if (md < 0) { hit_act(rx, ry, rw - pw - 40, rowH, tv_act, idx[i], 0); hit_act(px - 10, py - 10, pw + 20, ph + 20, off_act, 0, 0); } }
    else if (md < 0) hit_act(rx, ry, rw, rowH, tv_act, idx[i], 0); }
  { const char *al = T("Add a TV by its address"); float aw = text_width(al, F_SMALL - 1, 600, 0) + 30, ah = 54, ax = SB_W / 2 - aw / 2, ay = y + h - INS_B - 18 - ah; int pr = ph_pressed(ax, ay, aw, ah);
    text_draw(al, SB_W / 2, ay + ah / 2 - text_line_height(F_SMALL - 1) / 2.0f, F_SMALL - 1, 600, WHITE_A(pr ? 240 : 140), 0, 0, ALIGN_CENTER); if (md < 0) hit_act(ax, ay, aw, ah, ip_open, 0, 0); }
  gfx_opacity_pop(); gfx_opacity_pop();
}
static void sh_gone(void) { shOpen = 0; shCloseAt = 0; padIp = 0; atvCodeWait = 0; /* (an Android TV pairing: given up) */ pthread_mutex_lock(&mu); int pairing = CX.st == CX_PAIR; pthread_mutex_unlock(&mu); if (pairing) { pthread_mutex_lock(&mu); CX.stop = 1; pthread_mutex_unlock(&mu); } if (!cast_connected()) { free(pendingPlay); pendingPlay = NULL; } }
static const PhSheet castSheet = { sh_draw, NULL, sh_gone };

/* ---- the remote: what plays on the TV, its bar (a tap or a drag seeks), play/pause, 10 s back and on, stop, and
   the arrows for the TV's own pages ---- */
static float rmDrag = -1; /* a drag on the bar: where (0..1) */
static void rm_btn(float cx, float cy, float r, const char *icon, float isz, int solid, HitFn fn, int arg);
static int rmView; static Tween rmViewT; /* 0 the remote, 1 the subtitles, 2 the sound */
static void cmd(const char *s);
static void rm_view(int v, int b) { (void)b; rmView = v; if (v) cmd("{\"t\":\"tracks?\"}"); pplat_haptic_k(HK_TICK, 0.4f); } /* (the TV says its tracks again: never an empty list) */
static void rm_pick(int i, int kind) { char m[160]; pthread_mutex_lock(&mu); const char *id = kind == 1 ? (i < 0 ? "off" : CX.subs[i].id) : CX.auds[i].id; snprintf(m, sizeof m, "{\"t\":\"%s\",\"id\":\"%s\"}", kind == 1 ? "sub" : "audio", id);
  if (kind == 1) snprintf(CX.sub, sizeof CX.sub, "%s", id); else snprintf(CX.aud, sizeof CX.aud, "%s", id); pthread_mutex_unlock(&mu); cmd(m); pplat_haptic_k(HK_TICK, 0.6f); }
static void rm_sync(int a, int b) { (void)a; (void)b; cmd("{\"t\":\"subsync\"}"); pthread_mutex_lock(&mu); CX.syncing = 1; pthread_mutex_unlock(&mu); pplat_haptic_k(HK_TICK, 0.6f); }
static void rm_delay(int d, int b) { (void)b; pthread_mutex_lock(&mu); CX.delay = d == 0 ? 0 : CX.delay + d; int v = CX.delay; pthread_mutex_unlock(&mu); char m[80]; snprintf(m, sizeof m, "{\"t\":\"subdelay\",\"ms\":%d}", v); cmd(m); pplat_haptic_k(HK_TICK, 0.4f); }
static Scroll rmLv;
/* a list of the film's tracks: Off first (subtitles), each with where it comes from; the one on, lit */
/* the TV's subtitles: a line of languages (Off first, the one on, the preferred one, then the rest by name; each with how
   many), then that language's subtitles (each with where it comes from); the TV's sound tracks: one list. Their timing
   under the subtitles */
static char rmLang[64]; static Scroll rmChips; static float gLitX = -1, gLitW; static Tween rmListA; /* (the lit chip's pill; the list fading in as its tray changes) */
static void lang_key(const char *code, char *out, size_t cap) { char c[16]; const char *k = code && *code ? subs_lang_canon(code, c, sizeof c) : NULL; snprintf(out, cap, "%s", k && *k ? k : "?"); }
static const char *lang_title(const char *key) { const char *n = strcmp(key, "?") ? subs_lang_name(key) : NULL; return n && *n ? T(n) : T("Other"); }
static char rmKeys[24][64];
static void rm_lang_pick(int i, int b) { (void)b; if (i < 0) { rm_pick(-1, 1); return; } if (i < 24) { if (strcmp(rmLang, rmKeys[i])) { tween_set(&rmListA, 0); tween_to(&rmListA, 1, 0.22f, EASE_WEB); } snprintf(rmLang, sizeof rmLang, "%s", rmKeys[i]); rmLv.pos = 0; pplat_haptic_k(HK_TICK, 0.4f); } }
/* the subtitles' look on the TV, chosen by seeing it (as the player's): sizes as letters of those sizes, colours and
   outlines as their colour, backgrounds as a word on each, styled or plain; set here, the TV follows at once */
static const char *SY_POS[6] = { "3", "5", "8", "12", "18", "25" }; static const char *SY_SZ[7] = { "0", "1", "2", "3", "4", "5", "6" }, *SY_COL[3] = { "#ffffff", "#ffe600", "#00e5ff" }, *SY_OUT[2] = { "#000000", "#ffffff" }, *SY_BG[3] = { "0", "1", ".6" }, *SY_ASS[2] = { "styled", "plain" };
static void follow_tick(int justReady);
static void sy_pick(int kind, int i) { const char *k[6] = { "subtitleSize", "subsColor", "subsOutlineColor", "subsBgStyle", "subsAssStyle", "subsPosPct" }; const char *v = kind == 0 ? SY_SZ[i] : kind == 1 ? SY_COL[i] : kind == 2 ? SY_OUT[i] : kind == 3 ? SY_BG[i] : kind == 4 ? SY_ASS[i] : SY_POS[i];
  store_set(k[kind], v); follow_tick(1); pplat_haptic_k(HK_PICK, 0.8f); }
static const char *SY_BR[4] = { "100", "80", "60", "40" };
static int syFont; static Scroll rmSyS; static double syCloseAt; static Tween syFk[3]; /* syCloseAt: a font picked, its list folds then; syFk: each list's opening, eased */ /* syFont: a font's list open under its row (1 Latin, 2 Arabic) */
static void sy_fontopen(int kind, int b) { (void)b; syFont = syFont == kind ? 0 : kind; pplat_haptic_k(HK_TICK, 0.6f); }
static void sy_font(int kind, int i) { char v[8]; snprintf(v, sizeof v, "%d", i % 100); store_set(kind == 2 ? "subsFontAr" : "subsFont", v); follow_tick(1); pplat_haptic_k(HK_PICK, 0.8f); syCloseAt = now_s() + 0.28; } /* (its tick shown a moment, then the list folds away) */
static void sy_bright(int r, int i) { (void)r; if (i >= 0 && i < 4) { store_set("subsBright", SY_BR[i]); follow_tick(1); pplat_haptic_k(HK_PICK, 0.8f); } }
static void rm_style(float y, float hAll) { float x = PAD, w = SB_W - 2 * PAD, h = 96; const char *names[6] = { T("Size"), T("Colour"), T("Outline"), T("Background"), T("Styled subtitles"), T("Position") };
  const char *cur[6] = { store_get("subtitleSize", "2"), store_get("subsColor", "#ffffff"), store_get("subsOutlineColor", "#000000"), store_get("subsBgStyle", "0"), store_get("subsAssStyle", "styled"), store_get("subsPosPct", "8") };
  uint32_t tc = 0xff000000u | (uint32_t)strtoul(cur[1] + 1, NULL, 16), oc = 0xff000000u | (uint32_t)strtoul(cur[2] + 1, NULL, 16);
  pthread_mutex_lock(&mu); int scope = CX.scope, pics = CX.pics, ar = CX.subAr; pthread_mutex_unlock(&mu); if (!ar && syFont == 2) syFont = 0;
  float top = y, bot = y + hAll - 10; gfx_clip_push(0, top - 6, SB_W, bot - top + 6); ph_drag(0, top, SB_W, bot - top, &rmSyS, 1); scroll_tick(&rmSyS); y = top - rmSyS.pos;
  /* what the TV's subtitles can't take: greyed, one line why (as the player's tray) */
  if (scope) { const char *why = scope == 2 ? (pics ? T("These subtitles are pictures: their look can\xe2\x80\x99t be changed.") : T("The TV draws these subtitles: their look can\xe2\x80\x99t be changed.")) : T("Styled subtitles keep their own fonts, colours and background.");
    int nl = text_wrap_count(why, w - 40, 3, F_SMALL, 600, 0); text_draw_wrapped(why, x + 20, y + 4, w - 40, 3, F_SMALL, 600, TXT2, 0, ALIGN_START, 34); y += nl * 34 + 22; }
  /* the rows: size; the fonts (each a list under its row, the Arabic one while Arabic subtitles are on); colour, outline,
     background, brightness; styled or plain; position */
  static const int ORD[] = { 0, 10, 11, 1, 2, 3, 12, 4, 5 };
  for (int oi = 0; oi < 9; oi++) { int r = ORD[oi]; if (r == 11 && !ar) continue;
    int look = r == 1 || r == 3 || r == 10 || r == 11, off = (scope == 2 && r != 4) || (scope == 1 && look); int h0 = hit_count(); if (off) gfx_opacity_push(0.35f);
    if (r == 10 || r == 11) { int kind = r == 10 ? 1 : 2, fc = kind == 1 ? atoi(store_get("subsFont", "0")) : atoi(store_get("subsFontAr", "0")); if (fc < 0 || fc >= SUBF_N) fc = 0; /* a font: its name in itself (an Arabic one with a word in it) */
      const char *nm = fc ? (kind == 1 ? SUBF_LAT[fc] : SUBF_AR[fc]) : T("Default"); char vb[96]; snprintf(vb, sizeof vb, kind == 2 ? "%s  \xd9\x85\xd8\xb1\xd8\xad\xd8\xa8\xd8\xa7" : "%s", nm); int wt = kind == 1 ? text_sub_weight(700, fc, 0) : text_sub_weight(700, 0, fc);
      float pk = press_k(x, y, w, h); gfx_rrect(x, y, w, h, 24, WHITE_A(pk > 0 ? (int)(8 + 18 * pk) : 8)); text_draw(T(kind == 1 ? "Font" : "Arabic font"), x + 26, y + h / 2 - text_line_height(F_SMALL) / 2.0f, F_SMALL, 600, WHITE_A(230), 0, w * 0.4f, ALIGN_START);
      if (syCloseAt > 0 && now_s() >= syCloseAt) { syCloseAt = 0; syFont = 0; } tween_to(&syFk[kind], syFont == kind && !off ? 1 : 0, 0.32f, EASE_WEB); tween_tick(&syFk[kind], phDt); float fk = syFk[kind].v; /* (the list opens and folds, never at once) */
      text_draw(vb, x + w - 70, y + h / 2 - text_line_height(F_SMALL + 2) / 2.0f, F_SMALL + 2, wt, ACC2, 0, w * 0.5f, ALIGN_END); icon_draw_rot("ph_chev", x + w - 56, y + h / 2 - 16, 32, WHITE_A(140), 90 * fk);
      hit_act(x, y, w, h, sy_fontopen, kind, 0); y += h + 8;
      if (fk > 0.002f && !off) { float lh = 72, full = SUBF_N * lh + 8, y0 = y, hk = full * fk; int hn = hit_count(); gfx_clip_push(0, y0, SB_W, hk); gfx_opacity_push(fminf(1, fk * 1.4f)); gfx_offset_push(0, -(1 - fk) * 24); for (int i = 0; i < SUBF_N; i++) { const char *n2 = i ? (kind == 1 ? SUBF_LAT[i] : SUBF_AR[i]) : T("Default"); int w2 = kind == 1 ? text_sub_weight(600, i, 0) : text_sub_weight(600, 0, i), on = i == fc; float p2 = press_k(x + 24, y, w - 24, lh - 6);
          gfx_rrect(x + 24, y, w - 24, lh - 6, 18, on ? col_alpha(ACC, 0.24f) : WHITE_A(p2 > 0 ? (int)(6 + 20 * p2) : 5)); text_draw(n2, x + 50, y + (lh - 6) / 2 - text_line_height(F_SMALL + 1) / 2.0f, F_SMALL + 1, w2, WHITE_A(on ? 255 : 220), 0, w * 0.5f, ALIGN_START);
          if (kind == 2) text_draw("\xd9\x85\xd8\xb1\xd8\xad\xd8\xa8\xd8\xa7", x + w - (on ? 84 : 30), y + (lh - 6) / 2 - text_line_height(F_SMALL + 2) / 2.0f, F_SMALL + 2, w2, WHITE_A(200), 0, 0, ALIGN_END);
          if (on) icon_draw("ph_check", x + w - 62, y + (lh - 6) / 2 - 18, 36, ACC2); hit_act(x + 24, y, w - 24, lh - 6, sy_font, kind, i); y += lh; } gfx_offset_pop(); gfx_opacity_pop(); gfx_clip_pop(); if (fk < 0.98f) hit_trim(hn); /* (taps only once it is open) */ y = y0 + hk; }
      if (off) { gfx_opacity_pop(); hit_trim(h0); } continue; }
    int n = r == 0 ? 7 : r == 2 || r == 4 ? 2 : r == 5 ? 6 : r == 12 ? 4 : 3; gfx_rrect(x, y, w, h, 24, WHITE_A(8)); float lw = w * 0.36f; const char *nm = r == 12 ? T("Brightness") : names[r];
    { float fp = ph_fit_px(nm, F_SMALL, 600, 0, lw - 34); text_draw(nm, x + 26, y + h / 2 - text_line_height((int)fp) / 2.0f, (int)fp, 600, WHITE_A(230), 0, lw - 30, ALIGN_START); }
    float ax = x + lw, aw = w - lw - 10, cw2 = aw / n, cy = y + h / 2;
    for (int i = 0; i < n; i++) { float cx = ax + cw2 * i + cw2 / 2;
      if (r == 12) { const char *bv = store_get("subsBright", "100"); int on = !strcmp(bv, SY_BR[i]); float k = atoi(SY_BR[i]) / 100.0f, pk = press_k(cx - cw2 / 2, y, cw2, h); gfx_scale_push(1 - 0.08f * pk, 1 - 0.08f * pk, cx, cy); /* each as bright as it makes them */
        float bw2 = fminf(cw2 - 12, 92), bh2 = 54; gfx_rrect(cx - bw2 / 2, cy - bh2 / 2, bw2, bh2, 12, on ? col_alpha(ACC, 0.36f) : WHITE_A(12)); text_draw("Aa", cx, cy - text_line_height(24) / 2.0f, 24, 700, col_mix(0xff000000u, tc, k), 0, 0, ALIGN_CENTER); if (on) gfx_ring(cx - bw2 / 2 - 4, cy - bh2 / 2 - 4, bw2 + 8, bh2 + 8, 15, 2.5f, WHITE_A(235));
        gfx_scale_pop(); hit_act(cx - cw2 / 2, y, cw2, h, sy_bright, 0, i); continue; }
      const char *v = r == 0 ? SY_SZ[i] : r == 1 ? SY_COL[i] : r == 2 ? SY_OUT[i] : r == 3 ? SY_BG[i] : r == 4 ? SY_ASS[i] : SY_POS[i]; int on = r == 1 || r == 2 ? !strcasecmp(cur[r], v) : !strcmp(cur[r], v); if (r == 5) { int c = atoi(cur[5]), bi = 0; for (int q = 1; q < 6; q++) if (abs(atoi(SY_POS[q]) - c) < abs(atoi(SY_POS[bi]) - c)) bi = q; on = i == bi; } /* (a height set a percent at a time in the player: the nearest step lit) */ float pk = press_k(cx - cw2 / 2, y, cw2, h);
      gfx_scale_push(1 - 0.08f * pk, 1 - 0.08f * pk, cx, cy);
      if (r == 0) { int px = 16 + i * 4; float rr = fminf(cw2 / 2 - 2, 28); if (on) gfx_circle(cx, cy, rr, col_alpha(ACC, 0.4f)); text_draw("A", cx, cy - text_line_height(px) / 2.0f, px, 800, on ? WHITE_A(255) : WHITE_A(160), 0, 0, ALIGN_CENTER); }
      else if (r == 1 || r == 2) { uint32_t c = 0xff000000u | (uint32_t)strtoul(v + 1, NULL, 16); gfx_circle(cx, cy, 20, c); gfx_ring(cx - 20, cy - 20, 40, 40, 20, 1.5f, r == 2 && i == 0 ? WHITE_A(90) : BLACK_A(120)); if (on) gfx_ring(cx - 28, cy - 28, 56, 56, 28, 3, WHITE_A(235)); }
      else if (r == 3) { float bw2 = fminf(cw2 - 16, 110), bh2 = 50, bx = cx - bw2 / 2, by = cy - bh2 / 2, bo = (float)atof(v); gfx_rrect(bx, by, bw2, bh2, 12, RGB(0x4a, 0x5a, 0x6e)); if (bo > 0) gfx_rrect(bx + 10, by + 8, bw2 - 20, bh2 - 16, 6, BLACK_A((int)(bo * 255)));
        for (int d = 0; d < 4 && bo == 0; d++) { static const float ox[4] = { -1.5f, 1.5f, 0, 0 }, oy[4] = { 0, 0, -1.5f, 1.5f }; text_draw("Aa", cx + ox[d], cy - text_line_height(24) / 2.0f + oy[d], 24, 700, oc, 0, 0, ALIGN_CENTER); }
        text_draw("Aa", cx, cy - text_line_height(24) / 2.0f, 24, 700, tc, 0, 0, ALIGN_CENTER); if (on) gfx_ring(bx - 5, by - 5, bw2 + 10, bh2 + 10, 16, 3, WHITE_A(235)); }
      else if (r == 5) { float bw2 = fminf(cw2 - 10, 72), bh2 = 54, bx = cx - bw2 / 2, by = cy - bh2 / 2, f = (float)atof(v) / 25.0f; gfx_rrect(bx, by, bw2, bh2, 10, on ? col_alpha(ACC, 0.4f) : WHITE_A(12)); gfx_rrect(bx + 12, by + bh2 - 10 - (bh2 - 22) * f, bw2 - 24, 4, 2, WHITE_A(on ? 255 : 170)); if (on) gfx_ring(bx - 4, by - 4, bw2 + 8, bh2 + 8, 13, 2.5f, WHITE_A(235)); } /* (how high: a line at that height in a little screen) */
      else { const char *lb = i ? T("Plain") : T("Styled"); float bw2 = fminf(cw2 - 16, 170), bh2 = 54; gfx_rrect(cx - bw2 / 2, cy - bh2 / 2, bw2, bh2, bh2 / 2, on ? WHITE_A(240) : WHITE_A(14)); text_draw(lb, cx, cy - text_line_height(F_SMALL - 1) / 2.0f, F_SMALL - 1, 700, on ? RGB(14, 12, 20) : TXT2, 0, bw2 - 16, ALIGN_CENTER); }
      gfx_scale_pop(); hit_act(cx - cw2 / 2, y, cw2, h, sy_pick, r, i); }
    if (off) { gfx_opacity_pop(); hit_trim(h0); } y += h + 8; }
  rmSyS.max = (y + rmSyS.pos) - bot + 20; if (rmSyS.max < 0) rmSyS.max = 0; gfx_clip_pop(); }
/* a live channel on the TV: its place in the line-up (the channels it was picked among), the one before or after
   started from here as the player's Up / Down does (found on the phone, played on the TV) */
static int rm_live(void) { return live_type(castType); }
static const LiveCh *rm_live_ch(void) { int n = live_lineup_n(); for (int i = 0; i < n; i++) { const LiveCh *c = live_lineup_item(i); if (c && !strcmp(c->id, castId)) return c; } return NULL; }
static void rm_ch_pick(int i, int b) { (void)b; int n = live_lineup_n(); if (i < 0 || i >= n) return; const LiveCh *c = live_lineup_item(i); if (!c) return; Item t; live_item(c, &t); live_start(&t, NULL, 0, 0); pplat_haptic_k(HK_TICK, 0.6f); }
static void rm_ch(int d, int b) { (void)b; int n = live_lineup_n(); if (n < 2) return; int c = -1; for (int i = 0; i < n; i++) { const LiveCh *l = live_lineup_item(i); if (l && !strcmp(l->id, castId)) c = i; } if (c < 0) c = live_lineup_cur(); if (c < 0) c = 0; rm_ch_pick(((c + d) % n + n) % n, 0); }
static void rm_ch_btn(float x, float cy, float r, int sd) { int ok = live_lineup_n() > 1; if (!ok) gfx_opacity_push(0.35f); rm_btn(x, cy, r, NULL, 0, 0, ok ? rm_ch : NULL, sd); float k = 1 - 0.07f * press_k(x - r, cy - r, 2 * r, 2 * r), is = r * 1.3f; gfx_scale_push(k, k, x, cy); icon_draw_rot("p_next", x - is / 2, cy - is / 2, is, WHITE_A(240), sd < 0 ? 180 : 0); gfx_scale_pop(); if (!ok) gfx_opacity_pop(); }
static Scroll rmChS;
static void rm_channels(float y, float h) { float cw = SB_W - 2 * PAD; { float r = 28, cx = PAD + r, cy = y + 40; rm_btn(cx, cy, r, "ph_back", 30, 0, rm_view, 0); text_draw(T("Channels"), cx + r + 20, cy - text_line_height(F_H2 - 6) / 2.0f, F_H2 - 6, 800, TXT, -0.2f, cw - 2 * r - 20, ALIGN_START); }
  float top = y + 96, bot = y + h - 20, rh = 92; int n = live_lineup_n(); gfx_clip_push(0, top, SB_W, bot - top); ph_drag(0, top, SB_W, bot - top, &rmChS, 1); scroll_tick(&rmChS); float ry = top - rmChS.pos;
  for (int i = 0; i < n; i++, ry += rh + 10) { if (ry + rh < top - 10 || ry > bot + 10) continue; const LiveCh *c = live_lineup_item(i); if (!c) continue; int on = !strcmp(c->id, castId), pr = ph_pressed(PAD, ry, cw, rh);
    gfx_rrect(PAD, ry, cw, rh, rh / 2, on ? col_alpha(ACC, 0.26f) : WHITE_A(pr ? 26 : 10)); if (on) gfx_ring(PAD, ry, cw, rh, rh / 2, 1.5f, col_alpha(ACC2, 0.75f));
    float ls = rh - 24; gfx_circle(PAD + 12 + ls / 2, ry + rh / 2, ls / 2, WHITE_A(16)); { float asp = 0; GLuint t = c->logo[0] ? img_get(c->logo, (int)ls, (int)ls, &asp) : 0; if (t && asp > 0) { float lw = ls * 0.8f, lh = lw / asp; if (lh > ls * 0.6f) { lh = ls * 0.6f; lw = lh * asp; } gfx_image(t, PAD + 12 + ls / 2 - lw / 2, ry + rh / 2 - lh / 2, lw, lh, 0, WHITE_A(255), 0, 0, 1, 1); } }
    text_draw(c->name, PAD + 12 + ls + 20, ry + rh / 2 - text_line_height(F_BODY) / 2.0f, F_BODY, 700, TXT, 0, cw - ls - 90, ALIGN_START);
    if (on) { float lx = PAD + cw - 70; gfx_circle(lx, ry + rh / 2, 6, RGB(0xff, 0x45, 0x3a)); }
    hit_act(PAD, ry, cw, rh, rm_ch_pick, i, 0); }
  rmChS.max = (ry + rmChS.pos) - bot; if (rmChS.max < 0) rmChS.max = 0; gfx_clip_pop(); }
static void rm_tracks_body(int kind, float y, float h);
static void rm_tracks(int kind, float y, float h) { float cw = SB_W - 2 * PAD; if (kind == 4) { rm_channels(y, h); return; }
  { float r = 28, cx = PAD + r, cy = y + 40; rm_btn(cx, cy, r, "ph_back", 30, 0, rm_view, 0); /* back, then a switch: Subtitles | Audio (its lit part slides) */
    const char *lb2[3] = { T("Subtitles"), T("Audio"), T("Style") }; float sw = fminf(cw - 2 * r - 24, 560), sh = 56, sx = PAD + 2 * r + 24 + (cw - 2 * r - 24 - sw) / 2, sy = cy - sh / 2, hw = sw / 3;
    static Tween segT; tween_to(&segT, kind - 1, 0.26f, EASE_WEB); tween_tick(&segT, phDt);
    gfx_rrect(sx, sy, sw, sh, sh / 2, WHITE_A(12)); gfx_rrect(sx + 4 + segT.v * hw, sy + 4, hw - 8, sh - 8, (sh - 8) / 2, WHITE_A(240));
    for (int k = 0; k < 3; k++) { float k2 = fmaxf(0, 1 - fabsf(segT.v - k)); text_draw(lb2[k], sx + hw * k + hw / 2, cy - text_line_height(F_SMALL) / 2.0f, F_SMALL, 750, col_mix(TXT2, RGB(14, 12, 20), k2), 0, hw - 16, ALIGN_CENTER); hit_act(sx + hw * k, sy, hw, sh, rm_view, k + 1, 0); } }
  { static int lastK = -1; static Tween kA; if (kind != lastK) { if (lastK >= 0) { tween_set(&kA, 0); tween_to(&kA, 1, 0.24f, EASE_WEB); } else tween_set(&kA, 1); lastK = kind; } tween_tick(&kA, phDt); /* another tab: its content fades in, never swapped in one frame */
    if (kind == 3) { gfx_opacity_push(kA.v); gfx_offset_push(0, 12 * (1 - kA.v)); rm_style(y + 100, h - 100); gfx_offset_pop(); gfx_opacity_pop(); return; }
    if (kind == 4) { rm_channels(y, h); return; }
    if (kA.v < 0.999f) { gfx_opacity_push(kA.v); gfx_offset_push(0, 12 * (1 - kA.v)); rm_tracks_body(kind, y, h); gfx_offset_pop(); gfx_opacity_pop(); return; } }
  rm_tracks_body(kind, y, h); }
static void rm_tracks_body(int kind, float y, float h) { float cw = SB_W - 2 * PAD;
  pthread_mutex_lock(&mu); int n = kind == 1 ? CX.nsub : CX.naud; char cur[64]; snprintf(cur, sizeof cur, "%s", kind == 1 ? CX.sub : CX.aud); int dl = CX.delay;
  static struct { char id[64], label[96], lang[16], from[64]; } L[200]; int nl = 0; for (int i = 0; i < n && nl < 200; i++) { if (kind == 1) memcpy(&L[nl++], &CX.subs[i], sizeof L[0]); else { snprintf(L[nl].id, 64, "%s", CX.auds[i].id); snprintf(L[nl].label, 96, "%s", CX.auds[i].label); snprintf(L[nl].lang, 16, "%s", CX.auds[i].lang); L[nl].from[0] = 0; nl++; } } pthread_mutex_unlock(&mu);
  float top = y + 96, bot = y + h - (kind == 1 ? 156 : 20); /* (the timing and Sync with room above them) */
  static int show[200]; int ns = 0; int curOff = kind == 1 && (!strcmp(cur, "off") || !cur[0]);
  if (kind == 1) { /* trays as the player's: Off, the file's own, then each addon's (its name), each with how many; a tray's
       subtitles listed with the preferred language first, then by language */
    char keys[24][64]; int cnt[24], nk = 0; for (int i = 0; i < nl; i++) { const char *k = !strncmp(L[i].id, "emb:", 4) ? "\001" : L[i].from[0] ? L[i].from : "?"; int f = -1; for (int q = 0; q < nk; q++) if (!strcmp(keys[q], k)) f = q; if (f < 0 && nk < 24) { f = nk++; snprintf(keys[f], 64, "%s", k); cnt[f] = 0; } if (f >= 0) cnt[f]++; }
    for (int q = 1; q < nk; q++) if (!strcmp(keys[q], "\001")) { char t[64]; int tc = cnt[q]; memcpy(t, keys[q], 64); for (int r = q; r > 0; r--) { memcpy(keys[r], keys[r - 1], 64); cnt[r] = cnt[r - 1]; } memcpy(keys[0], t, 64); cnt[0] = tc; break; } /* (the file's own first) */
    char onK[64] = ""; for (int i = 0; i < nl; i++) if (!strcmp(cur, L[i].id)) snprintf(onK, sizeof onK, "%s", !strncmp(L[i].id, "emb:", 4) ? "\001" : L[i].from);
    int have = 0; for (int q = 0; q < nk; q++) if (!strcmp(keys[q], rmLang)) have = 1; if (!have) snprintf(rmLang, sizeof rmLang, "%s", onK[0] ? onK : nk ? keys[0] : "");
    for (int q = 0; q < nk && q < 24; q++) snprintf(rmKeys[q], sizeof rmKeys[q], "%s", keys[q]);
    float chH = 56, cy0 = top + 4, gap = 12; float tot = 0; char lbs[25][96];
    for (int q = 0; q < nk; q++) snprintf(lbs[q], 96, "%s  %d", !strcmp(keys[q], "\001") ? T("In the file") : keys[q], cnt[q]);
    float wds[25]; for (int q = 0; q < nk; q++) { wds[q] = text_width(lbs[q], F_SMALL - 1, 700, 0) + 44 + (onK[0] && !strcmp(keys[q], onK) ? 16 : 0); tot += wds[q] + gap; }
    ph_drag(0, cy0, SB_W, chH, &rmChips, 0); scroll_tick(&rmChips); rmChips.max = tot - gap - cw > 0 ? tot - gap - cw : 0;
    gfx_clip_push(0, cy0 - 6, SB_W, chH + 12); float cx = PAD - rmChips.pos;
    { float lx = PAD - rmChips.pos, litX = -1, litW = 0; for (int q = 0; q < nk; q++) { if (!strcmp(keys[q], rmLang)) { litX = lx; litW = wds[q]; } lx += wds[q] + gap; } /* the lit one: a white pill that glides from chip to chip (it jumped, its words flipping colour at once) */
      static Tween pX, pW; static int pSeen; if (litX >= 0) { if (!pSeen || rmViewT.v < 0.05f) { tween_set(&pX, litX + rmChips.pos); tween_set(&pW, litW); pSeen = 1; } tween_to(&pX, litX + rmChips.pos, 0.26f, EASE_WEB); tween_to(&pW, litW, 0.26f, EASE_WEB); }
      tween_tick(&pX, phDt); tween_tick(&pW, phDt); gLitX = pX.v - rmChips.pos; gLitW = pW.v; if (litX >= 0) gfx_rrect(gLitX, cy0, gLitW, chH, chH / 2, WHITE_A(240)); else gLitW = 0; }
    for (int q = 0; q < nk; q++) { int here = onK[0] && !strcmp(keys[q], onK); /* (a dot: the tray of the one on) */
      int pr = ph_pressed(cx, cy0, wds[q], chH); if (!(gLitW > 0 && fabsf(gLitX - cx) < 1 && fabsf(gLitW - wds[q]) < 1)) gfx_rrect(cx, cy0, wds[q], chH, chH / 2, WHITE_A(pr ? 30 : 12));
      float ov = 0; if (gLitW > 0) { float a0 = fmaxf(cx, gLitX), a1 = fminf(cx + wds[q], gLitX + gLitW); ov = clampf((a1 - a0) / wds[q], 0, 1); } /* (how much of the white pill is over it: its words dark as much) */
      float tx0 = cx + wds[q] / 2 - (here ? 8 : 0); text_draw(lbs[q], tx0, cy0 + chH / 2 - text_line_height(F_SMALL - 1) / 2.0f, F_SMALL - 1, 700, col_mix(TXT2, RGB(14, 12, 20), ov), 0, 0, ALIGN_CENTER);
      if (here) gfx_circle(cx + wds[q] - 22, cy0 + chH / 2, 5, ACC2 | 0xff000000u);
      hit_act(cx, cy0, wds[q], chH, rm_lang_pick, q, 0); cx += wds[q] + gap; }
    gfx_clip_pop(); top += chH + 26;
    char pref[16]; lang_key(store_get("subsLang", ""), pref, sizeof pref);
    for (int i = 0; i < nl && ns < 200; i++) { const char *k = !strncmp(L[i].id, "emb:", 4) ? "\001" : L[i].from[0] ? L[i].from : "?"; if (!strcmp(k, rmLang)) show[ns++] = i; }
    for (int a2 = 0; a2 < ns; a2++) for (int b2 = a2 + 1; b2 < ns; b2++) { char ka[16], kb[16]; lang_key(L[show[a2]].lang, ka, sizeof ka); lang_key(L[show[b2]].lang, kb, sizeof kb);
      int ra = !strcmp(ka, pref) ? 0 : 1, rb = !strcmp(kb, pref) ? 0 : 1; if (rb < ra || (rb == ra && strcmp(lang_title(kb), lang_title(ka)) < 0)) { int t = show[a2]; show[a2] = show[b2]; show[b2] = t; } } }
  else for (int i = 0; i < nl; i++) show[ns++] = i;
  { static int seen; if (!seen) { seen = 1; tween_set(&rmListA, 1); } tween_tick(&rmListA, phDt); } float la = kind == 1 ? rmListA.v : 1; gfx_opacity_push(la); gfx_offset_push(0, 10 * (1 - la)); /* (another tray: its list fades in, never swapped in one frame) */
  float rh = kind == 1 ? 72 : 84; gfx_clip_push(0, top, SB_W, bot - top); ph_drag(0, top, SB_W, bot - top, &rmLv, 1); scroll_tick(&rmLv); float ry = top - rmLv.pos;
  if (!nl) { spinner(SB_W / 2, top + 60, 16); }
  for (int si = kind == 1 ? -1 : 0; si < ns; si++, ry += rh + 8) { int i = si < 0 ? -1 : show[si]; int on = si < 0 ? curOff : !strcmp(cur, L[i].id); float rx = PAD - 8, rw = cw + 16; /* (subtitles: Off, the first row of every tray) */
    if (ry + rh > top - 10 && ry < bot + 10) { int pr = ph_pressed(rx, ry, rw, rh); gfx_rrect(rx, ry, rw, rh, rh / 2, on ? col_alpha(ACC, 0.26f) : WHITE_A(pr ? 26 : 10)); if (on) gfx_ring(rx, ry, rw, rh, rh / 2, 1.5f, col_alpha(ACC2, 0.75f));
      /* its name without the language the chip already says ("English · SDH" -> "SDH"); none left: its place in the list */
      char lb[128]; const char *raw = i < 0 ? T("Off") : L[i].label[0] ? L[i].label : L[i].lang;
      if (*raw) snprintf(lb, sizeof lb, "%s", raw); else snprintf(lb, sizeof lb, "%s %d", T(kind == 1 ? "Subtitle" : "Track"), si + 1);
      if (i >= 0) { int same = 0, ord = 0; for (int q = 0; q < ns; q++) { const char *r2 = L[show[q]].label[0] ? L[show[q]].label : L[show[q]].lang; if (!strcmp(r2, raw)) { same++; if (q <= si) ord = same; } } if (same > 1) { size_t l = strlen(lb); snprintf(lb + l, sizeof lb - l, " %d", ord); } } /* (the same name more than once: numbered, as the player's) */
      const char *fr = kind == 1 || i < 0 ? "" : L[i].from; /* (subtitles: their group's name says where they come from) */
      float tw = rw - 60 - (fr[0] ? text_width(fr, F_TINY + 1, 700, 0) + 40 : 0) - 50; text_draw(lb, rx + 30, ry + rh / 2 - text_line_height(F_BODY - 2) / 2.0f, F_BODY - 2, on ? 800 : 600, on ? TXT : TXT2, 0, tw, ALIGN_START);
      if (fr[0]) { float fw = text_width(fr, F_TINY + 1, 700, 0) + 26, fx = rx + rw - 30 - fw - (on ? 40 : 0); gfx_rrect(fx, ry + rh / 2 - 19, fw, 38, 19, WHITE_A(14)); text_draw(fr, fx + 13, ry + rh / 2 - text_line_height(F_TINY + 1) / 2.0f, F_TINY + 1, 700, TXT3, 0, 0, ALIGN_LEFT); } /* (where it comes from: the film, or an addon) */
      if (on) icon_draw("ph_check", rx + rw - 30 - 30, ry + rh / 2 - 16, 32, ACC2 | 0xff000000u);
      hit_act(rx, ry, rw, rh, rm_pick, i, kind); } }
  rmLv.max = (ry + rmLv.pos) - bot; if (rmLv.max < 0) rmLv.max = 0; gfx_clip_pop(); gfx_offset_pop(); gfx_opacity_pop();
  if (kind == 1) { float dy = y + h - 96, cx = SB_W / 2; char v[24]; snprintf(v, sizeof v, "%+.1f s", dl / 1000.0); /* (their timing: earlier or later, a tenth at a time; Auto sync beside it, one group in the middle) */
    pthread_mutex_lock(&mu); int can = CX.canSync, sy = CX.syncing; char ss[120]; snprintf(ss, sizeof ss, "%s", CX.syncSt); pthread_mutex_unlock(&mu);
    const char *lb = T("Auto sync"); float r = 34, vw = 130, gap = 18, sh2 = 60, sw2 = text_width(lb, F_SMALL - 1, 700, 0) + 44 + (sy ? 30 : 0), gw = 2 * r + gap + vw + gap + 2 * r + 28 + sw2; if (gw > cw) { vw -= gw - cw; if (vw < 96) vw = 96; gw = 2 * r + gap + vw + gap + 2 * r + 28 + sw2; }
    float gx = cx - gw / 2, mx = gx + r, vx = gx + 2 * r + gap + vw / 2, px = gx + 2 * r + gap + vw + gap + r, sx2 = gx + gw - sw2, sy2 = dy - sh2 / 2;
    rm_btn(mx, dy, r, "ph_back", 0, 0, rm_delay, -100); gfx_rrect(mx - 11, dy - 1.5f, 22, 3, 1.5f, WHITE_A(235)); /* (drawn: crisp at any size) */
    rm_btn(px, dy, r, "ph_back", 0, 0, rm_delay, 100); gfx_rrect(px - 11, dy - 1.5f, 22, 3, 1.5f, WHITE_A(235)); gfx_rrect(px - 1.5f, dy - 11, 3, 22, 1.5f, WHITE_A(235));
    text_draw(v, vx, dy - text_line_height(F_BODY) / 2.0f, F_BODY, 800, dl ? TXT : TXT3, 0, 0, ALIGN_CENTER); hit_act(vx - vw / 2, dy - 30, vw, 60, rm_delay, 0, 0);
    { if (!can) gfx_opacity_push(0.35f); float pk = press_k(sx2, sy2, sw2, sh2); /* (the TV syncs them to the speech, as the player's Sync) */
      gfx_scale_push(1 - 0.06f * pk, 1 - 0.06f * pk, sx2 + sw2 / 2, dy); gfx_rrect(sx2, sy2, sw2, sh2, sh2 / 2, sy ? col_alpha(ACC, 0.36f) : WHITE_A(14 + (int)(20 * pk))); gfx_ring(sx2, sy2, sw2, sh2, sh2 / 2, 1, WHITE_A(26));
      if (sy) spinner(sx2 + 28, dy, 9); text_draw(lb, sx2 + 22 + (sy ? 30 : 0), dy - text_line_height(F_SMALL - 1) / 2.0f, F_SMALL - 1, 700, TXT, 0, 0, ALIGN_LEFT); gfx_scale_pop(); if (can) hit_act(sx2, sy2, sw2, sh2, rm_sync, 0, 0); else gfx_opacity_pop(); } /* (always there by the timing; dim when this subtitle cannot be synced, an addon's can) */
    if (ss[0]) { static Tween ssA; static char ssLast[120]; if (strcmp(ss, ssLast)) { snprintf(ssLast, sizeof ssLast, "%s", ss); tween_set(&ssA, 0); tween_to(&ssA, 1, 0.3f, EASE_WEB); } tween_tick(&ssA, phDt); /* what the TV says of the sync: one quiet line under the row, never over the list */
      float fp = ph_fit_px(ss, F_TINY + 1, 600, 0, cw); gfx_opacity_push(ssA.v); text_draw(ss, cx, dy + sh2 / 2 + 10, fp, 600, TXT3, 0, cw, ALIGN_CENTER); gfx_opacity_pop(); } } }
static void rm_play(int a, int b) { (void)a; (void)b; pthread_mutex_lock(&mu); int playing = !strcmp(CX.ts, "playing"); pthread_mutex_unlock(&mu); play_want(!playing); pplat_haptic_k(HK_TICK, 0.6f); }
static void rm_jump(int d, int b) { (void)b; { int sd = d < 0 ? -1 : 1; jbN = jbDir == sd && now_s() - jbAt < 1.2 ? jbN + 1 : 1; jbDir = sd; jbAt = now_s(); tween_set(&jbA, 0); tween_to(&jbA, 1, 0.45f, EASE_OUT); } pthread_mutex_lock(&mu); double p = CX.pos + d; if (p < 0) p = 0; if (CX.dur > 0 && p > CX.dur - 1) p = CX.dur - 1; CX.pos = p; CX.posAt = now_s(); pthread_mutex_unlock(&mu); char m[80]; snprintf(m, sizeof m, "{\"t\":\"seek\",\"pos\":%.1f}", p); cmd(m); pplat_haptic_k(HK_TICK, 0.5f); }
static void fmt_t(double s, char *o, size_t c) { int t = (int)(s + 0.5); if (t >= 3600) snprintf(o, c, "%d:%02d:%02d", t / 3600, t / 60 % 60, t % 60); else snprintf(o, c, "%d:%02d", t / 60, t % 60); }
/* a round control: glass, pressed it gives a little */
static void rm_meta_cb(cJSON *m, void *ud) { (void)m; (void)ud; }
static void rm_btn(float cx, float cy, float r, const char *icon, float isz, int solid, HitFn fn, int arg) { float pk = press_k(cx - r, cy - r, 2 * r, 2 * r), k = 1 - 0.07f * pk; gfx_scale_push(k, k, cx, cy);
  if (solid) { gfx_shadow(cx - r, cy - r + 8, 2 * r, 2 * r, r, 26, BLACK_A(90)); gfx_circle(cx, cy, r, WHITE_A(248)); } else { gfx_circle(cx, cy, r, WHITE_A(14 + (int)(24 * pk))); gfx_ring(cx - r, cy - r, 2 * r, 2 * r, r, 1, WHITE_A(26)); }
  if (icon) icon_draw(icon, cx - isz / 2, cy - isz / 2, isz, solid ? RGB(14, 12, 20) : WHITE_A(235)); gfx_scale_pop(); if (fn) hit_act(cx - r - 6, cy - r - 6, 2 * r + 12, 2 * r + 12, fn, arg, 0); }
/* the remote, sized to what it holds (at most 88 % of the screen, gliding as that changes):
   playing: the TV's name and Disconnect, the picture with its logo, the bar, then one row: subtitles and audio, 10 s
   back, play/pause, 10 s on, stop. Nothing playing (stopped here or with the TV's remote, or ended): the TV's name on
   the app's glows, as its home is. Subtitles and audio: one panel, a switch between the two, its list as long as it is */
static Orbs rmOrbs; static float rmHH = -1;
static int rm_idle(const char *ts) { return !ts[0] || !strcmp(ts, "idle") || !strcmp(ts, "ended"); }
static float rm_cw(void) { return fminf(SB_W - 2 * PAD, 680); }
static float rm_tracks_h(int kind) { pthread_mutex_lock(&mu); int n = 0; if (kind == 2) n = CX.naud; else { int any = 0; for (int i = 0; i < CX.nsub; i++) { const char *k = !strncmp(CX.subs[i].id, "emb:", 4) ? "\001" : CX.subs[i].from[0] ? CX.subs[i].from : "?"; if (!strcmp(k, rmLang)) n++; any++; } if (!n) n = any; } pthread_mutex_unlock(&mu); /* (subtitles: the tray shown) */
  if (kind == 3) return 100 + 6 * 104 + 30 + INS_B;
  if (kind == 4) { int n = live_lineup_n(); if (n < 3) n = 3; if (n > 8) n = 8; return 96 + n * 102 + 40 + INS_B; }
  if (kind == 1) n++; /* (Off) */ if (n < 2) n = 2; return 96 + (kind == 1 ? 82 + 156 : 20) + n * (kind == 1 ? 80 : 92) + 40 + INS_B; }
static void rm_stop_home(int a, int b) { (void)a; (void)b; cmd("{\"t\":\"stop\"}"); cmd("{\"t\":\"key\",\"k\":\"home\"}"); pthread_mutex_lock(&mu); snprintf(CX.ts, sizeof CX.ts, "idle"); pthread_mutex_unlock(&mu); orbs_push(&rmOrbs, ORB_BACK, 1); pplat_haptic_k(HK_TICK, 0.7f); } /* (the TV's player closed and its Home shown; here its home at once) */
/* the remote's buttons: subtitles and audio (round, as stop is, both signs in it); 10 s back or on (as the player's: a
   little swell, the arrow turning its way and back, how far over it for a moment); play/pause; stop (a square) */
static void rm_cc_btn(float bx, float cy, int hasT, float r) { if (!hasT) gfx_opacity_push(0.35f); rm_btn(bx, cy, r, NULL, 0, 0, hasT ? rm_view : NULL, 1);
  float k = 1 - 0.07f * press_k(bx - r, cy - r, 2 * r, 2 * r); gfx_scale_push(k, k, bx, cy); float is = r * 0.62f; icon_draw("p_cc", bx - 3 - is, cy - is / 2, is, WHITE_A(240)); gfx_rrect(bx - 1, cy - is * 0.36f, 2, is * 0.72f, 1, WHITE_A(80)); icon_draw("p_spk", bx + 3, cy - is / 2, is, WHITE_A(240)); gfx_scale_pop(); if (!hasT) gfx_opacity_pop(); }
static void rm_seek_btn(float x, float cy, float r, int sd) { float on = jbDir == sd && jbA.v < 1, bk = on ? 1 + 0.14f * sinf(jbA.v * (float)M_PI) : 1, rr = on ? sd * 40 * sinf(jbA.v * (float)M_PI) : 0, is = r * 1.27f;
  gfx_scale_push(bk, bk, x, cy); rm_btn(x, cy, r, NULL, 0, 0, rm_jump, sd * 10); float k = 1 - 0.07f * press_k(x - r, cy - r, 2 * r, 2 * r); gfx_scale_push(k, k, x, cy);
  icon_draw_rot(sd < 0 ? "p_rw" : "p_ff", x - is / 2, cy - is / 2, is, WHITE_A(240), rr); text_draw("10", x, cy - text_line_height(14) / 2.0f + 4, 14, 800, WHITE_A(240), 0, 0, ALIGN_CENTER); gfx_scale_pop(); gfx_scale_pop();
  float la = jbDir == sd ? (float)((1.1 - (now_s() - jbAt)) / 0.3) : 0; if (la > 1) la = 1;
  if (la > 0) { char t[16]; float e = jbA.v * 2 > 1 ? 1 : jbA.v * 2; snprintf(t, sizeof t, "%s%d s", sd < 0 ? "\xe2\x88\x92" : "+", 10 * jbN); gfx_opacity_push(la); text_draw(t, x, cy - r - 44 - 10 * (1 - e), 26, 800, WHITE_A(250), 0, 0, ALIGN_CENTER); gfx_opacity_pop(); } }
static void rm_play_btn(float cx, float cy, float r, int playing) { static Tween pp; tween_to(&pp, playing ? 1 : 0, 0.22f, EASE_OUT_BACK); tween_tick(&pp, phDt); float sc = 0.86f + 0.14f * fabsf(pp.v * 2 - 1); gfx_scale_push(sc, sc, cx, cy); rm_btn(cx, cy, r, playing ? "p_pause" : "p_play", r * 0.9f, 1, rm_play, 0); gfx_scale_pop(); }
static void rm_stop_btn(float sx, float cy, float r) { rm_btn(sx, cy, r, NULL, 0, 0, rm_stop_home, 0); float q = r * 0.56f * (1 - 0.07f * press_k(sx - r, cy - r, 2 * r, 2 * r)); gfx_rrect(sx - q / 2, cy - q / 2, q, q, 4, WHITE_A(235)); }
static float flyTx, flyTy = -1, flyTw, flyTh; static int rmDrew; /* (the mini player's place, and when the remote was last drawn: the picture flies over whichever is on top) */
static void fly_draw(float x, float y, float h); static void morph_draw(float e, float x, float y, float h); static void morph_panel(float e, float x, float y, float h); static void morph_art(float e, float x, float y, float h); float ph_sheet_pulled(void); static float rmMorphK;
static struct { float x, y, w, h, k, sx, sy, sw, sh; int on; double at; } FLY; /* x..h: its picture; sx..sh: the remote's panel, both as they were let go */ static float rmLastA; /* the remote let go while a title plays: its picture flies into the mini player's (from where it was) */
static void rm_draw(float a) {
  if (0 && rmOpen && a < rmLastA - 0.002f && rmLastA > 0.5f && !rmView && FLY.w > 0) { pthread_mutex_lock(&mu); int act = !strcmp(CX.ts, "playing") || !strcmp(CX.ts, "paused"); pthread_mutex_unlock(&mu);
    if (act) { rmOpen = 0; FLY.on = 1; FLY.at = now_s(); if (rmMorphK > 0 && flyTy >= 0) { float e = rmMorphK, tw = flyTh * 16 / 9; /* (pulled part way already: it goes on from there) */
      FLY.sx += (flyTx - FLY.sx) * e; FLY.sy += (flyTy - FLY.sy) * e; FLY.sw += (flyTw - FLY.sw) * e; FLY.sh += (flyTh - FLY.sh) * e; FLY.x += (flyTx - FLY.x) * e; FLY.y += (flyTy - FLY.y) * e; FLY.w += (tw - FLY.w) * e; FLY.h += (flyTh - FLY.h) * e; } rmMorph = 0; rmMorphK = 0; } } /* (closing: the mini player comes at once, the picture going into it) */
  rmLastA = a; rmDrew = 1;
  if (FLY.on) { if (flyTy >= 0) fly_draw(flyTx, flyTy, flyTh); return; } /* (going into the mini player: the panel itself shrinks there, nothing slides down) */
  pthread_mutex_lock(&mu); char ts[16], title[200], name[96]; snprintf(ts, sizeof ts, "%s", CX.ts); snprintf(title, sizeof title, "%s", CX.title); snprintf(name, sizeof name, "%s", CX.name); double pos = CX.pos, dur = CX.dur, at = CX.posAt; int st = CX.st, hasT = CX.nsub + CX.naud > 0; pthread_mutex_unlock(&mu);
  if (st != CX_READY) { ph_sheet_close(); return; }
  int playing = !strcmp(ts, "playing"), idle = rm_idle(ts); if (playing && at > 0) pos += now_s() - at; if (dur > 0 && pos > dur) pos = dur;
  if (idle && rmView) rmView = 0; /* (nothing plays: no tracks to pick) */
  float cw = rm_cw(), x0 = (SB_W - cw) / 2, maxH = SB_H * 0.88f, head = 104;
  float fixed = head + 70 + 150 + 20 + INS_B, artH = fminf(cw * 9 / 16, maxH - fixed - 24); if (artH < 280) artH = 0; else fixed -= 110; /* (the picture holds every button: under it only the bar; a low screen, no picture: the buttons in one row under the bar) */ /* (a low screen: no picture, the controls first) */
  float idleH = fminf(cw * 9 / 16, fmaxf(160, maxH - head - 40 - INS_B));
  float want = rmView ? rm_tracks_h(rmView) : idle ? head + idleH + 40 + INS_B : fixed + (artH > 0 ? artH + 24 : 64); if (want > maxH) want = maxH;
  if (rmHH < 0 || a < 0.05f) rmHH = want; rmHH += (want - rmHH) * clampf(phDt * 12, 0, 1); if (fabsf(want - rmHH) < 0.5f) rmHH = want;
  float pulled = ph_sheet_pulled(); { int canM = 0; /* (no shrinking into the mini player: the remote goes down as any sheet, the mini player comes up after it) */ rmMorphK = canM && pulled > 0 ? clampf(pulled / (SB_H * 0.42f), 0, 1) : 0; rmMorph = rmMorphK > 0.002f; }
  { static float pwV = -1; float pwWant = rmView ? SB_W - 24 : cw + 2 * 40; /* (the remote: the panel hugs its controls; the tracks' lists: the room they use) */ if (pwV < 0 || a < 0.05f) pwV = pwWant; pwV += (pwWant - pwV) * clampf(phDt * 12, 0, 1); if (fabsf(pwWant - pwV) < 0.5f) pwV = pwWant; gsW = pwV; }
  float h = rmHH, y = glass_sheet(h, a), in = ease_apply(EASE_OUT, clampf(a, 0, 1)); gsW = -1; FLY.sx = gsX; FLY.sy = y - pulled; FLY.sw = gsPW; FLY.sh = h - INS_B + 10;
  if (rmMorph) { FLY.x = x0; FLY.y = FLY.sy + head; FLY.w = cw; FLY.h = artH; morph_panel(rmMorphK, flyTx, flyTy, flyTh); y = FLY.sy; gfx_opacity_push(clampf(1 - rmMorphK * 3.5f, 0, 1)); } /* (pulled down: the panel shrinks toward the mini player under the finger, its buttons and words fading where they were, its picture going with it; let go far enough it goes on into it, else back) */
  tween_to(&rmViewT, rmView ? 1 : 0, 0.32f, EASE_WEB); tween_tick(&rmViewT, phDt); float vk = rmViewT.v; static int lastView = 1; if (rmView) lastView = rmView;
  gfx_clip_push(0, y, SB_W, SB_H - y);
  if (vk > 0.001f) { gfx_opacity_push(in * vk); gfx_offset_push(SB_W * 0.25f * (1 - vk), 0); rm_tracks(lastView, y + 20, h - INS_B - 40); gfx_offset_pop(); gfx_opacity_pop(); if (vk > 0.5f) { gfx_clip_pop(); return; } }
  gfx_opacity_push(in * (1 - vk)); gfx_offset_push(-SB_W * 0.15f * vk, 0);
  /* the TV: its name, and Disconnect */
  { float ch = 56, nw = fminf(text_width(name, F_SMALL, 700, 0), cw * 0.55f), cwid = nw + 18 + 32 + 12 + 22; gfx_rrect(x0, y + 30, cwid, ch, ch / 2, col_alpha(ACC, 0.18f)); icon_draw("ph_cast_on", x0 + 18, y + 30 + ch / 2 - 16, 32, ACC2 | 0xff000000u);
    text_draw(name, x0 + 18 + 32 + 12, y + 30 + ch / 2 - text_line_height(F_SMALL) / 2.0f, F_SMALL, 700, TXT, 0, nw, ALIGN_START);
    const char *dl = T("Disconnect"); float pw = text_width(dl, F_SMALL - 1, 700, 0) + 34, px = x0 + cw - pw; int pr = ph_pressed(px, y + 30, pw, ch); text_draw(dl, px + pw / 2, y + 30 + ch / 2 - text_line_height(F_SMALL - 1) / 2.0f, F_SMALL - 1, 700, WHITE_A(pr ? 240 : 150), 0, 0, ALIGN_CENTER); hit_act(px - 8, y + 22, pw + 16, ch + 16, off_act, 0, 0); }
  static Tween idT; tween_to(&idT, idle ? 1 : 0, 0.4f, EASE_WEB); tween_tick(&idT, phDt); float ik = idT.v;
  /* nothing plays: the TV's home, the app's glows drifting under its name */
  if (ik > 0.001f) { float cy0 = y + head, ch = idleH; gfx_opacity_push(ik); orbs_step(&rmOrbs, phDt, 1, 1, 2.6f); gfx_rrect(x0, cy0, cw, ch, 30, WHITE_A(8)); orbs_draw_in(&rmOrbs, 0.85f, x0, cy0, cw, ch, 30); gfx_ring(x0, cy0, cw, ch, 30, 1, WHITE_A(22));
    icon_draw("ph_cast_on", SB_W / 2 - 30, cy0 + ch / 2 - 62, 60, WHITE_A(230)); text_draw(name, SB_W / 2, cy0 + ch / 2 + 14, F_H2 - 4, 800, WHITE_A(240), -0.2f, cw - 60, ALIGN_CENTER); gfx_opacity_pop(); }
  if (ik < 0.999f) { gfx_opacity_push(1 - ik);
  /* what plays: its picture, its logo (or name), a spinner while it starts */
  float ay = y + head; const cJSON *mt = castId[0] ? sb_meta_cached(castType, castId) : NULL;
  { static char asked[128]; char k[128]; snprintf(k, sizeof k, "%s:%s", castType, castId); if (!mt && castId[0] && strcmp(k, asked)) { snprintf(asked, sizeof asked, "%s", k); sb_meta(castType, castId, rm_meta_cb, NULL); } } /* (its artwork asked for once) */
  const LiveCh *lch = rm_live() ? rm_live_ch() : NULL;
  if (artH > 0) { const char *bg = js_str(mt, "background", js_str(mt, "poster", lch ? lch->poster : "")); GLuint t = bg[0] ? img_get_shaped(bg, (int)cw, (int)artH, 30, 1) : 0;
    if (!FLY.on && !rmMorph) { FLY.x = x0; FLY.y = ay; FLY.w = cw; FLY.h = artH; } if (rmMorph) gfx_opacity_push(0); /* (its picture: drawn shrinking, at the end) */
    gfx_shadow(x0, ay + 14, cw, artH, 30, 40, BLACK_A(110)); if (!t || !ph_picture(t, x0, ay, cw, artH, 30, WHITE_A(255))) { gfx_rrect(x0, ay, cw, artH, 30, WHITE_A(10)); icon_draw("ph_film", SB_W / 2 - 32, ay + artH / 2 - 32, 64, WHITE_A(70)); }
    gfx_rrect(x0, ay, cw, artH, 30, BLACK_A(60)); gfx_rrect_v(x0, ay, cw, artH * 0.45f, 30, BLACK_A(170), BLACK_A(0)); gfx_rrect_v(x0, ay + artH * 0.5f, cw, artH * 0.5f, 30, BLACK_A(0), BLACK_A(215)); /* (dark at the top for its name, at the foot for the stream, a little all over for the buttons) */ if (rmMorph) gfx_opacity_pop();
    /* its title, as the TV's player shows it: the logo (else the name), the episode ("S1 E4 · its name") or the
       year, then the stream in a few small chips; from the foot up */
    { char inf[96]; pthread_mutex_lock(&mu); snprintf(inf, sizeof inf, "%s", CX.pinfo); struct { char t[100], i[16]; int b, sep; } ch[8]; int nch = CX.nchip; memcpy(ch, CX.chip, sizeof ch); pthread_mutex_unlock(&mu);
      float bx0 = x0 + 26, by = ay + artH - 24, tlw = cw - 52;
      if (nch) { /* the TV player's own info line, as two plain lines from the foot up: the stream (resolution bold · picture and sound · size), then the sound playing and the subtitles on, each with its sign; a line too long for the room gets a smaller size, never cut */
        int split = nch; for (int q = 0; q < nch; q++) if (ch[q].sep) { split = q; break; }
        const char *dot = "  \xc2\xb7  "; float avail = cw - 52;
        for (int row = 1; row >= 0; row--) { int a0 = row ? split + 1 : 0, a1 = row ? nch : split; if (a0 >= a1) continue;
          int px = F_SMALL; float tot = 0;
          for (; px >= F_TINY - 6; px--) { tot = 0; int k = 0; for (int q = a0; q < a1; q++) { if (ch[q].sep || !ch[q].t[0]) continue; if (k++) tot += row ? px * 1.2f : text_width(dot, px, 600, 0); if (ch[q].i[0]) tot += px + 8; tot += text_width(ch[q].t, px, ch[q].b ? 800 : 600, 0); } if (tot <= avail) break; }
          float lh2 = text_line_height(px); by -= lh2 + 4; float cx2 = bx0; int k = 0;
          for (int q = a0; q < a1; q++) { if (ch[q].sep || !ch[q].t[0]) continue;
            if (k++) { if (row) cx2 += px * 1.2f; else cx2 += text_draw(dot, cx2, by, px, 600, WHITE_A(150), 0, 0, ALIGN_LEFT); }
            if (ch[q].i[0]) { icon_draw(ch[q].i, cx2, by + lh2 / 2 - px / 2.0f, px, WHITE_A(200)); cx2 += px + 8; }
            float room = bx0 + avail - cx2; if (room < 20) break;
            cx2 += text_draw(ch[q].t, cx2, by, px, ch[q].b ? 800 : 600, WHITE_A(ch[q].b ? 255 : 225), 0, room, ALIGN_LEFT); } }
        by -= 10; }
      else if (inf[0]) { float chh = 34, cx2 = bx0; char tmp[96]; snprintf(tmp, sizeof tmp, "%s", inf); char *sv = NULL; by -= chh;
        for (char *tk = strtok_r(tmp, "\xc2\xb7", &sv); tk; tk = strtok_r(NULL, "\xc2\xb7", &sv)) { while (*tk == ' ') tk++; size_t L = strlen(tk); while (L && tk[L - 1] == ' ') tk[--L] = 0; if (!*tk) continue;
          float w2 = text_width(tk, F_TINY, 700, 0.3f) + 22; if (cx2 + w2 > x0 + cw - 20) break; gfx_rrect(cx2, by, w2, chh, 9, WHITE_A(34)); gfx_ring(cx2, by, w2, chh, 9, 1, WHITE_A(40));
          text_draw(tk, cx2 + 11, by + chh / 2 - text_line_height(F_TINY) / 2.0f, F_TINY, 700, WHITE_A(235), 0.3f, 0, ALIGN_LEFT); cx2 += w2 + 8; }
        by -= 12; }
      char sub[200] = ""; { int se = 0, ep = 0; const char *cc = strchr(castVid, ':'); if (!strcmp(castType, "series") && cc && sscanf(cc, ":%d:%d", &se, &ep) == 2) { const char *en = ""; const cJSON *v;
          cJSON_ArrayForEach(v, js_arr(mt, "videos")) if (!strcmp(js_str(v, "id", ""), castVid)) { en = js_str(v, "name", js_str(v, "title", "")); break; }
          snprintf(sub, sizeof sub, "S%d E%d%s%s", se, ep, *en ? "  \xc2\xb7  " : "", en); }
        else { const char *yr = js_str(mt, "releaseInfo", js_str(mt, "year", "")); if (*yr) snprintf(sub, sizeof sub, "%.4s", yr); } }

      const char *lg = js_str(mt, "logo", lch ? lch->logo : ""); float asp = 0; GLuint lt = lg[0] ? img_get(lg, (int)(tlw * 0.6f), 90, &asp) : 0;
      float ty = ay + 24; /* its name at the top: the logo (else the name), then the episode or the year */
      if (lt && asp > 0) { float lh2 = fminf(60, artH * 0.17f), lw2 = lh2 * asp; if (lw2 > tlw * 0.6f) { lw2 = tlw * 0.6f; lh2 = lw2 / asp; } gfx_image(lt, bx0, ty, lw2, lh2, 0, WHITE_A(255), 0, 0, 1, 1); ty += lh2 + 8; }
      else if (title[0]) { float lh = text_line_height(F_H2 - 4); text_draw(title, bx0, ty, F_H2 - 4, 800, WHITE_A(250), -0.3f, tlw, ALIGN_START); ty += lh + 4; }
      if (rm_live()) { const char *lv = T("LIVE"); float lw3 = text_width(lv, F_TINY, 800, 0.6f) + 26, lh3 = 34; gfx_rrect(bx0, ty + 2, lw3, lh3, 8, RGB(0xe5, 0x2d, 0x27)); text_draw(lv, bx0 + 13, ty + 2 + lh3 / 2 - text_line_height(F_TINY) / 2.0f, F_TINY, 800, WHITE_A(255), 0.6f, 0, ALIGN_LEFT); } /* (a channel: LIVE, red, as the player's corner) */
      else if (sub[0]) text_draw(sub, bx0, ty, F_SMALL, 700, WHITE_A(225), 0, tlw, ALIGN_START);
      /* play and the jumps, in the picture's middle (between its name and the stream), as a player's */
      { float mid = ay + artH * 0.5f, sc = fminf(1, artH / 380), sp = fminf(cw / 4.9f, 144); tween_tick(&jbA, phDt); /* subtitles and audio, 10 s back, play/pause, 10 s on, stop: one row across the picture's middle */
        for (int q = -2; q <= 2; q++) if (q) gfx_circle(SB_W / 2 + q * sp, mid, (abs(q) == 2 ? 44 : 46) * sc, BLACK_A(110)); /* (a dark disc under each: clear on any picture) */
        rm_cc_btn(SB_W / 2 - 2 * sp, mid, hasT, 44 * sc); for (int sd = -1; sd <= 1; sd += 2) { if (rm_live()) rm_ch_btn(SB_W / 2 + sd * sp, mid, 46 * sc, sd); else rm_seek_btn(SB_W / 2 + sd * sp, mid, 46 * sc, sd); } /* (a channel: the one before and the next, as the player's) */ rm_play_btn(SB_W / 2, mid, 58 * sc, playing); rm_stop_btn(SB_W / 2 + 2 * sp, mid, 44 * sc); } }
    float p2pW = 0; { char pl[160]; pthread_mutex_lock(&mu); snprintf(pl, sizeof pl, "%s", CX.p2p); pthread_mutex_unlock(&mu); /* a torrent: its peers and speed, top right (as the player's corner) */
      if (pl[0]) { int px = F_TINY; float tw2 = text_width(pl, px, 600, 0); while (tw2 > cw * 0.5f && px > F_TINY - 6) { px--; tw2 = text_width(pl, px, 600, 0); } float pw = tw2 + 22 + 20, ph = 40, pxx = x0 + cw - 18 - pw, pyy = ay + 18;
        gfx_rrect(pxx, pyy, pw, ph, ph / 2, BLACK_A(130)); gfx_ring(pxx, pyy, pw, ph, ph / 2, 1, WHITE_A(36)); gfx_circle(pxx + 18, pyy + ph / 2, 5, RGB(0x4c, 0xd9, 0x64)); text_draw(pl, pxx + 30, pyy + ph / 2 - text_line_height(px) / 2.0f, px, 600, WHITE_A(235), 0, tw2 + 4, ALIGN_LEFT); p2pW = pw + 10; } }
    { pthread_mutex_lock(&mu); int pw = CX.pw, pwT = CX.pwT; pthread_mutex_unlock(&mu); static Tween pwA, pwV; tween_to(&pwA, pw >= 0 ? 1 : 0, 0.3f, EASE_WEB); tween_tick(&pwA, phDt); if (pw >= 0) { tween_to(&pwV, pwT > 0 ? fminf(1, pw / (float)pwT) : 0, 0.6f, EASE_OUT); } tween_tick(&pwV, phDt); /* (its number: the TV's own, as its screen shows it; the fill: how far to the start) */
      if (pwA.v > 0.01f) { /* the TV waiting for the film's seek previews: a chip, top right, its pictures made so far filling it; Play starts the film now */
        char pc[16]; snprintf(pc, sizeof pc, "%d%%", pw < 0 ? 0 : pw); float tw2 = text_width(pc, F_TINY, 700, 0), pw2 = 18 + 28 + 8 + tw2 + 18, ph = 40, pxx = x0 + cw - 18 - pw2 - p2pW, pyy = ay + 18;
        gfx_opacity_push(pwA.v); gfx_rrect(pxx, pyy, pw2, ph, ph / 2, BLACK_A(140)); gfx_clip_push(pxx, pyy, pw2 * pwV.v, ph); gfx_rrect(pxx, pyy, pw2, ph, ph / 2, col_alpha(ACC, 0.45f)); gfx_clip_pop(); gfx_ring(pxx, pyy, pw2, ph, ph / 2, 1, WHITE_A(36));
        icon_draw("ph_film", pxx + 16, pyy + ph / 2 - 14, 28, WHITE_A(235)); text_draw(pc, pxx + 16 + 28 + 8, pyy + ph / 2 - text_line_height(F_TINY) / 2.0f, F_TINY, 700, WHITE_A(240), 0, 0, ALIGN_LEFT); gfx_opacity_pop(); p2pW += (pw2 + 10) * pwA.v; } }
    if (!strcmp(ts, "choosing") || !strcmp(ts, "loading") || !strcmp(ts, "error")) { float sh = 44, sx2 = x0 + cw - 20 - sh / 2 - p2pW; gfx_circle(sx2, ay + 20 + sh / 2, sh / 2, BLACK_A(150)); if (strcmp(ts, "error")) spinner(sx2, ay + 20 + sh / 2, 10); else gfx_circle(sx2, ay + 20 + sh / 2, 7, RGB(0xef, 0x8f, 0x8a)); }
    ay += artH + 24; }
  else { text_draw(title, x0, ay + 4, F_H2 - 4, 800, TXT, -0.2f, cw, ALIGN_START); ay += 64; }
  /* a channel: no bar (nothing to seek), its catalog and the line-up to pick from */
  if (rm_live()) { float by = ay + 20, cy = by + 14; const char *cat = live_catalog_of(castId); gfx_circle(x0 + 8, cy, 6, RGB(0xe5, 0x2d, 0x27)); text_draw(cat && *cat ? cat : T("LIVE"), x0 + 24, cy - text_line_height(F_SMALL - 1) / 2.0f, F_SMALL - 1, 700, TXT2, 0, cw - 220, ALIGN_START);
    if (live_lineup_n() > 1) { const char *lb = T("Channels"); float pw = text_width(lb, F_SMALL - 1, 700, 0) + 44, ph = 56, px = x0 + cw - pw, py = cy - ph / 2, pk = press_k(px, py, pw, ph); gfx_scale_push(1 - 0.06f * pk, 1 - 0.06f * pk, px + pw / 2, cy);
      gfx_rrect(px, py, pw, ph, ph / 2, WHITE_A(14 + (int)(20 * pk))); gfx_ring(px, py, pw, ph, ph / 2, 1, WHITE_A(26)); text_draw(lb, px + pw / 2, cy - text_line_height(F_SMALL - 1) / 2.0f, F_SMALL - 1, 700, TXT, 0, 0, ALIGN_CENTER); gfx_scale_pop(); hit_act(px, py, pw, ph, rm_view, 4, 0); }
    if (artH <= 0) { float cy2 = by + 120, cx = SB_W / 2, sp = fminf(cw / 4.6f, 132); rm_cc_btn(cx - 2 * sp, cy2, hasT, 38); for (int sd = -1; sd <= 1; sd += 2) rm_ch_btn(cx + sd * sp, cy2, 44, sd); rm_play_btn(cx, cy2, 60, playing); rm_stop_btn(cx + 2 * sp, cy2, 38); }
    gfx_opacity_pop(); gfx_offset_pop(); gfx_opacity_pop(); gfx_clip_pop(); if (rmMorph) { gfx_opacity_pop(); morph_art(rmMorphK, flyTx, flyTy, flyTh); } return; }
  /* the bar: a tap or a drag seeks */
  float bx = x0, bw = cw, by = ay + 20; float fx, fy, fx0, fy0; int held; int down = ph_finger(&fx, &fy, &fx0, &fy0, &held);
  { static Scroll barH, barV; barH.max = barV.max = 0; ph_drag(bx - 20, by - 44, bw + 40, 88, &barH, 0); ph_drag(bx - 20, by - 44, bw + 40, 88, &barV, 1); } /* (the seek bar keeps its finger, whichever way it drifts: the sheet is never pulled by a seek) */
  if (down && dur > 0 && fabsf(fy0 - by) < 44 && fx0 >= bx - 20 && fx0 <= bx + bw + 20) rmDrag = clampf((fx - bx) / bw, 0, 1);
  else if (!down && rmDrag >= 0) { double p = rmDrag * dur; char m[80]; snprintf(m, sizeof m, "{\"t\":\"seek\",\"pos\":%.1f}", p); cmd(m); pthread_mutex_lock(&mu); CX.pos = p; CX.posAt = now_s(); pthread_mutex_unlock(&mu); rmDrag = -1; pplat_haptic_k(HK_TICK, 0.5f); }
  { static Tween thk; tween_to(&thk, rmDrag >= 0 ? 1 : 0, 0.18f, EASE_OUT); tween_tick(&thk, phDt); float pr = rmDrag >= 0 ? rmDrag : dur > 0 ? (float)(pos / dur) : 0, th = 6 + 6 * thk.v;
    gfx_rrect(bx, by - th / 2, bw, th, th / 2, WHITE_A(40)); gfx_rrect(bx, by - th / 2, bw * pr, th, th / 2, WHITE_A(240)); if (dur > 0) gfx_circle(bx + bw * pr, by, 9 + 7 * thk.v, WHITE_A(255));
    char a1[24], b1[24]; fmt_t(rmDrag >= 0 ? rmDrag * dur : pos, a1, sizeof a1); fmt_t(dur > pos ? dur - (rmDrag >= 0 ? rmDrag * dur : pos) : 0, b1 + 1, sizeof b1 - 1); b1[0] = '-';
    text_draw(dur > 0 ? a1 : "--:--", bx, by + 20, F_TINY + 1, 700, TXT3, 0, 0, ALIGN_START); text_draw(dur > 0 ? b1 : "--:--", bx + bw, by + 20, F_TINY + 1, 700, TXT3, 0, 0, ALIGN_END); }
  /* under the bar: subtitles and audio, stop (the picture holds the rest); a low screen, no picture: one row of all */
  if (artH <= 0) { float cy = by + 120, cx = SB_W / 2, sp = fminf(cw / 4.6f, 132); rm_cc_btn(cx - 2 * sp, cy, hasT, 38); tween_tick(&jbA, phDt); for (int sd = -1; sd <= 1; sd += 2) { if (rm_live()) rm_ch_btn(cx + sd * sp, cy, 44, sd); else rm_seek_btn(cx + sd * sp, cy, 44, sd); } rm_play_btn(cx, cy, 60, playing); rm_stop_btn(cx + 2 * sp, cy, 38); }
  gfx_opacity_pop(); }
  gfx_offset_pop(); gfx_opacity_pop(); gfx_clip_pop();
  if (rmMorph) { gfx_opacity_pop(); morph_art(rmMorphK, flyTx, flyTy, flyTh); }
}
static void rm_gone(void) { rmLastA = 0; rmOpen = 0; rmDrag = -1; rmView = 0; rmHH = -1; }
static const PhSheet remoteSheet = { rm_draw, NULL, rm_gone, 1500 };
/* the mini player, over the app's bar while a title plays on the TV (as the streaming apps keep theirs): its picture, its
   name and the TV's, play/pause and stop; how far along it is as a line at its foot; a tap anywhere else opens the remote */
/* the picture on its way from the remote into the mini player (x, y, h: the mini player's place), over everything */
void cast_mini_place(float x, float y, float w, float h) { flyTx = x; flyTy = y; flyTw = w; flyTh = h; } /* (where the mini player sits: every frame, shown or not) */
float cast_mini_fly_k(void) { if (!FLY.on) return -1; float k = (float)((now_s() - FLY.at) / 0.46); return k >= 1 ? 1 : ease_apply(EASE_OUT, k < 0 ? 0 : k); }
void cast_mini_fly(float x, float y, float h) { (void)x; (void)y; (void)h; extern int ph_sheet_shown(void); rmDrew = 0; if (rmOpen || ph_sheet_shown()) return; fly_draw(flyTx, flyTy, flyTh); } /* (the remote still drawn: it draws the picture over itself; gone: here, no frame without it) */ /* (the sheet drawn last frame: it draws the picture over itself) */
static void morph_draw(float e, float x, float y, float h);
static void fly_draw(float x, float y, float h) { if (!FLY.on) return; float k = (float)((now_s() - FLY.at) / 0.46); if (k >= 1) { FLY.on = 0; return; } morph_draw(ease_apply(EASE_OUT, k < 0 ? 0 : k), x, y, h); }
/* the panel and its picture e of the way (0..1) from where the remote let them go to the mini player's place */
static void morph_draw(float e, float x, float y, float h) { morph_panel(e, x, y, h); morph_art(e, x, y, h); }
static void morph_panel(float e, float x, float y, float h) { float pa = rmMorph ? 1 : e < 0.7f ? 1 : 1 - (e - 0.7f) / 0.3f, /* (held all the way while pulled, never the picture alone over the page; going in, it hands over to the mini player as that one comes up: the same shape, the same place) */ px = FLY.sx + (x - FLY.sx) * e, py = FLY.sy + (y - FLY.sy) * e, pw = FLY.sw + (flyTw - FLY.sw) * e, ph = FLY.sh + (h - FLY.sh) * e, pr = 46 + (34 - 46) * e; /* the panel: the remote's own glass, from its place and size to the mini player's, handing over to the mini player's at the end */
  extern void ph_glass_grab_liquid(void); extern void ph_liquid_bubble(float x, float y, float w, float h, float r, float press); gfx_opacity_push(pa); ph_glass_grab_liquid(); ph_liquid_bubble(px, py, pw, ph, pr, 0); gfx_rrect(px, py, pw, ph, pr, RGBA(14, 12, 20, 165)); gfx_ring(px, py, pw, ph, pr, 1, WHITE_A(30)); gfx_opacity_pop(); }
static void morph_art(float e, float x, float y, float h) { /* its picture: from the remote's to the mini player's, straight on its right at the end as the mini player's is */
  float tw = h * 16 / 9, fx = FLY.x + (x - FLY.x) * e, fy = FLY.y + (y - FLY.y) * e, fw = FLY.w + (tw - FLY.w) * e, fh = FLY.h + (h - FLY.h) * e, r = 30 + 4 * e;
  const cJSON *mt = castId[0] ? sb_meta_cached(castType, castId) : NULL; const char *bg = js_str(mt, "background", js_str(mt, "poster", "")); GLuint t = bg[0] ? img_get_shaped(bg, (int)FLY.w, (int)FLY.h, 30, 1) : 0; if (!t && bg[0]) t = img_get_shaped(bg, (int)(tw + 34), (int)h, 34, 1);
  gfx_shadow(fx, fy + 10, fw, fh, r, 30 * (1 - e), BLACK_A((int)(110 * (1 - e)))); gfx_clip_push(fx, fy, fw, fh); float ew = fw + 34 * e; if (t) gfx_image(t, fx, fy, ew, fh, r, WHITE_A(255), 0, 0, 1, 1); else gfx_rrect(fx, fy, ew, fh, r, WHITE_A(14));
  gfx_rrect_h(fx, fy, fw * 0.45f, fh, r, BLACK_A((int)(120 * e)), BLACK_A(0)); gfx_clip_pop(); }
int cast_mini_want(void) { if (rmOpen) return 0; pthread_mutex_lock(&mu); int on = CX.st == CX_READY && (!strcmp(CX.ts, "playing") || !strcmp(CX.ts, "paused") || !strcmp(CX.ts, "loading") || !strcmp(CX.ts, "choosing")); /* (choosing: the TV finding the best stream, the title and picture are the phone's own; error, ended, idle: gone) */ pthread_mutex_unlock(&mu); return on && castId[0]; }
static void mini_open(int a, int b) { (void)a; (void)b; rm_open(); }
void cast_mini_content(float x, float y, float w, float h) {
  pthread_mutex_lock(&mu); char ts[16], title[200], name[96]; snprintf(ts, sizeof ts, "%s", CX.ts); snprintf(title, sizeof title, "%s", CX.title); snprintf(name, sizeof name, "%s", CX.name); double pos = CX.pos, dur = CX.dur, at = CX.posAt; pthread_mutex_unlock(&mu);
  int playing = !strcmp(ts, "playing"); if (playing && at > 0) pos += now_s() - at; if (dur > 0 && pos > dur) pos = dur;
  const cJSON *mt = castId[0] ? sb_meta_cached(castType, castId) : NULL; const char *nm = title[0] ? title : js_str(mt, "name", "");
  { static char asked[128]; char k[128]; snprintf(k, sizeof k, "%s:%s", castType, castId); if (!mt && castId[0] && strcmp(k, asked)) { snprintf(asked, sizeof asked, "%s", k); sb_meta(castType, castId, rm_meta_cb, NULL); } } /* (its artwork asked for once) */
  hit_act(x, y, w - 170, h, mini_open, 0, 0);
  float ah = h, aw = ah * 16 / 9, ax = x, ay = y; /* its picture: the whole left side, the tray's own round corners there, round on its right too, a soft shade from the left */ const LiveCh *lch = live_type(castType) ? rm_live_ch() : NULL; const char *bg = js_str(mt, "background", js_str(mt, "poster", lch ? lch->poster : "")); GLuint t = bg[0] ? img_get_shaped(bg, (int)(aw + 34), (int)ah, 34, 1) : 0; /* (made 34 wider and cut straight: round on the left with the tray, straight on its right) */
  { gfx_clip_push(ax, ay, aw, ah); if (!t || !ph_picture(t, ax, ay, aw + 34, ah, 34, WHITE_A(255))) gfx_rrect(ax, ay, aw + 34, ah, 34, WHITE_A(14)); else { gfx_rrect_h(ax, ay, aw * 0.45f, ah, 34, BLACK_A(120), BLACK_A(0)); gfx_rrect_h(ax + aw * 0.55f, ay, aw * 0.45f + 1, ah, 0, BLACK_A(0), BLACK_A(150)); } gfx_clip_pop(); } /* (soft at both sides: a shade from the left, fading into the tray on the right) */
  if (lch && !bg[0] && lch->logo[0]) { float asp = 0; GLuint lt = img_get(lch->logo, (int)(aw * 0.6f), (int)(ah * 0.6f), &asp); if (lt && asp > 0) { float lw = aw * 0.6f, lh = lw / asp; if (lh > ah * 0.55f) { lh = ah * 0.55f; lw = lh * asp; } gfx_image(lt, ax + aw / 2 - lw / 2, ay + ah / 2 - lh / 2, lw, lh, 0, WHITE_A(255), 0, 0, 1, 1); } } /* (a channel with no picture: its logo) */
  float tx = ax + aw + 18, tw = w - (tx - x) - 170, l1 = text_line_height(F_SMALL + 2), l2 = text_line_height(F_TINY), ty = y + (h - 14) / 2 - (l1 + 4 + l2) / 2;
  text_draw(nm, tx, ty, F_SMALL + 2, 700, WHITE_A(245), 0, tw, ALIGN_LEFT); ty += 2;
  icon_draw("ph_cast_on", tx, ty + l1 + 2 + l2 / 2 - 10, 20, ACC2 | 0xff000000u); text_draw(name, tx + 26, ty + l1 + 2, F_TINY, 600, WHITE_A(150), 0, tw - 26, ALIGN_LEFT);
  float cy = y + (h - 14) / 2, sx = x + w - 16 - 34, px = sx - 34 - 12 - 34;
  gfx_circle(px, cy, 32, BLACK_A(120)); gfx_ring(px - 32, cy - 32, 64, 64, 32, 1, WHITE_A(40)); gfx_circle(sx, cy, 32, BLACK_A(120)); gfx_ring(sx - 32, cy - 32, 64, 64, 32, 1, WHITE_A(40)); /* (each on a dark disc: clear on any glass) */
  if (!strcmp(ts, "loading") || !strcmp(ts, "choosing")) spinner(px, cy, 15); else rm_btn(px, cy, 34, playing ? "p_pause" : "p_play", 38, 0, rm_play, 0);
  rm_btn(sx, cy, 34, NULL, 0, 0, rm_stop_home, 0); { float q = 19 * (1 - 0.07f * press_k(sx - 34, cy - 34, 68, 68)); gfx_rrect(sx - q / 2, cy - q / 2, q, q, 3.5f, WHITE_A(235)); } /* (stop: the square, as the remote's) */
  if (live_type(castType)) { float ly = y + h - 22; const char *lv = T("LIVE"); gfx_circle(tx + 5, ly, 5, RGB(0xe5, 0x2d, 0x27)); text_draw(lv, tx + 16, ly - text_line_height(F_TINY - 2) / 2.0f, F_TINY - 2, 800, RGB(0xff, 0x6a, 0x5f), 0.6f, 0, ALIGN_LEFT); }
  else if (dur > 0) { char a1[24], b1[24]; fmt_t(pos, a1, sizeof a1); fmt_t(dur, b1, sizeof b1); int fp = F_TINY - 2; float wa = text_width(a1, fp, 600, 0), wb = text_width(b1, fp, 600, 0), ly = y + h - 17, th = text_line_height(fp); /* how far: the time played, a line, the whole time */
    text_draw(a1, tx, ly + 2 - th / 2, fp, 600, WHITE_A(170), 0, 0, ALIGN_LEFT); text_draw(b1, x + w - 26, ly + 2 - th / 2, fp, 600, WHITE_A(120), 0, 0, ALIGN_RIGHT);
    float lx = tx + wa + 12, lw = x + w - 26 - wb - 12 - lx, f = (float)(pos / dur); if (lw > 20) { gfx_rrect(lx, ly, lw, 4, 2, WHITE_A(34)); gfx_rrect(lx, ly, fmaxf(4, lw * f), 4, 2, ACC2 | 0xff000000u); } } } /* (how far: a line inside it, clear of its edge) */
static void rm_open(void) { if (rmOpen) return; rmOpen = 1; cmd("{\"t\":\"tracks?\"}"); ph_sheet_open(&remoteSheet); }

/* the cast button: connected, the remote; else the TVs */
void cast_open(void) {
  if (cast_connected()) { rm_open(); return; } shOpen = 1; ph_sheet_open(&castSheet); scan();
#ifdef SB_MAC
  if (getenv("SB_ATV_PAD")) { atvCodeWait = 1; snprintf(atvCode, sizeof atvCode, "%s", getenv("SB_ATV_PAD")); } /* (the Mac preview: the Android TV code pad, to look at) */
#endif
}
void cast_init(void) { (void)forget_all_offline; live_remote_on = cast_connected; live_remote_play = cast_live; /* (casting: a channel started here plays on the TV) */ CX.tvIdx = -1;
#ifdef SB_MAC
  { const char *d = getenv("SB_REMOTE_DEMO"); if (d) { /* (the Mac preview: a connected TV, to look at the remote; d = playing | paused | idle | loading) */
      CX.st = CX_READY; snprintf(CX.name, sizeof CX.name, "Living room TV"); snprintf(CX.ts, sizeof CX.ts, "%s", d); snprintf(CX.title, sizeof CX.title, "The Matrix"); CX.pos = 1520; CX.dur = 8160; CX.posAt = 0;
      snprintf(castType, sizeof castType, "movie"); snprintf(castId, sizeof castId, "tt0133093"); snprintf(castVid, sizeof castVid, "tt0133093"); if (getenv("SB_REMOTE_LIVE")) { snprintf(castType, sizeof castType, "tv"); snprintf(CX.title, sizeof CX.title, "ABC News"); CX.dur = 0; CX.nchip = 0; CX.pinfo[0] = 0; } /* (a channel, to look at) */ snprintf(CX.pinfo, sizeof CX.pinfo, "1080p \xc2\xb7 HDR10 \xc2\xb7 DDP 5.1"); { const char *dt[6][2] = {{"1080p",""},{"HDR10 \xc2\xb7 DDP 5.1",""},{"2.1 GB",""},{"",""},{"English Dolby Digital Plus 5.1","p_spk"},{"English [SDH] \xc2\xb7 OpenSubtitles v3","p_cc"}}; CX.nchip = 6; for (int q = 0; q < 6; q++) { snprintf(CX.chip[q].t, 100, "%s", dt[q][0]); snprintf(CX.chip[q].i, 16, "%s", dt[q][1]); CX.chip[q].b = q == 0; CX.chip[q].sep = q == 3; } } snprintf(CX.p2p, sizeof CX.p2p, "%s", "38 peers \xc2\xb7 4.2 MB/s"); CX.canSync = 1;
      static const char *SL[][3] = { { "emb:1", "English", "en" }, { "emb:2", "English SDH", "en" }, { "s3", "English", "en" }, { "s4", "Espa\xc3\xb1ol", "es" }, { "s5", "Deutsch", "de" } };
      for (int i = 0; i < 5; i++) { snprintf(CX.subs[i].id, 64, "%s", SL[i][0]); snprintf(CX.subs[i].label, 96, "%s", SL[i][1]); snprintf(CX.subs[i].lang, 16, "%s", SL[i][2]); snprintf(CX.subs[i].from, 64, "%s", i < 2 ? "Embedded" : "OpenSubtitles"); } CX.nsub = 5; snprintf(CX.sub, sizeof CX.sub, "emb:1");
      static const char *AL[][3] = { { "a1", "English 5.1", "en" }, { "a2", "Fran\xc3\xa7" "ais 5.1", "fr" } };
      for (int i = 0; i < 2; i++) { snprintf(CX.auds[i].id, 64, "%s", AL[i][0]); snprintf(CX.auds[i].label, 96, "%s", AL[i][1]); snprintf(CX.auds[i].lang, 16, "%s", AL[i][2]); } CX.naud = 2; snprintf(CX.aud, sizeof CX.aud, "a1");
      if (getenv("SB_REMOTE_SCOPE")) { CX.scope = atoi(getenv("SB_REMOTE_SCOPE")); CX.pics = 1; } if (getenv("SB_REMOTE_AR")) CX.subAr = 1; if (getenv("SB_REMOTE_VIEW")) rmView = atoi(getenv("SB_REMOTE_VIEW")); CX.pw = getenv("SB_REMOTE_PW") ? atoi(getenv("SB_REMOTE_PW")) : -1; CX.pwT = 80; if (getenv("SB_REMOTE_SYNC")) { CX.canSync = 1; CX.syncing = 1; snprintf(CX.syncSt, sizeof CX.syncSt, "%s", getenv("SB_REMOTE_SYNC")); } } } /* (development: what the subtitles can take, Arabic ones, a tab of the remote open) */
#endif
}
