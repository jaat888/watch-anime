/* mollad_jaat service worker: the Home page (and its show list) opens from the
   device when the network is slow, but the NETWORK always wins when it answers
   within a moment, so "latest episode" and the lists are never stale.
   Nothing else is touched: video, HLS, /api/watch, accounts etc. go to the network. */
const V = "mj-shell-v2";
const WAIT = 2500;   // ms to wait for the network before showing the saved copy

self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", e => e.waitUntil((async () => {
  for (const k of await caches.keys()) if (k !== V) await caches.delete(k);
  await self.clients.claim();
})()));

self.addEventListener("fetch", e => {
  const r = e.request;
  if (r.method !== "GET") return;
  const u = new URL(r.url);
  if (u.origin !== location.origin) return;
  const nav = r.mode === "navigate" && (u.pathname === "/" || u.pathname === "/index.html");
  if (!nav && u.pathname !== "/api/shows") return;
  e.respondWith(netFirst(e, nav ? "/" : "/api/shows", r));
});

async function netFirst(e, key, req) {
  const c = await caches.open(V);
  const net = fetch(req).then(async res => {
    if (res && res.ok) { try { await c.put(key, res.clone()); } catch (_) {} }
    return res;
  }).catch(() => null);
  e.waitUntil(net);
  const hit = await c.match(key, { ignoreVary: true });
  if (!hit) return (await net) || new Response("Offline", { status: 503 });
  const res = await Promise.race([net, new Promise(r => setTimeout(() => r(null), WAIT))]);
  return res && res.ok ? res : hit;            // fresh from the server, else the saved copy
}
