/* mollad_jaat service worker: the Home page (and its show list) opens from the
   device at once and is refreshed silently in the background.  Nothing else
   is touched: video, HLS, /api/watch, accounts etc. always go to the network. */
const V = "mj-shell-v1";

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
  e.respondWith(swr(e, nav ? "/" : "/api/shows", r));
});

async function swr(e, key, req) {
  const c = await caches.open(V);
  const hit = await c.match(key, { ignoreVary: true });
  const net = fetch(req).then(async res => {
    if (res && res.ok) { try { await c.put(key, res.clone()); } catch (_) {} }
    return res;
  }).catch(() => null);
  if (hit) { e.waitUntil(net); return hit; }          // instant from the device, refresh behind it
  return (await net) || new Response("Offline", { status: 503 });
}
