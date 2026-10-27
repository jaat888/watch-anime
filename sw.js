/* mollad_jaat service worker.
   Only the app shell ("/") is handled: the NETWORK wins if it answers within a few
   seconds, otherwise the saved copy opens instantly (e.g. while a free host is waking up).
   Only a real copy of the app is ever saved - never a host wake-up/error page.
   Video, HLS and every /api call go straight to the network (the page keeps its own list cache). */
const V = "mj-shell-v3";
const WAIT = 4000;   // ms to wait for the network before showing the saved copy

self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", e => e.waitUntil((async () => {
  for (const k of await caches.keys()) if (k !== V) await caches.delete(k);
  await self.clients.claim();
})()));

self.addEventListener("fetch", e => {
  const r = e.request, u = new URL(r.url);
  if (r.method !== "GET" || u.origin !== location.origin) return;
  if (r.mode === "navigate" && (u.pathname === "/" || u.pathname === "/index.html")) e.respondWith(shell(e, r));
});

async function isApp(res) {
  if (!res || !res.ok || !(res.headers.get("content-type") || "").includes("text/html")) return false;
  try { return (await res.clone().text()).includes('id="app"'); } catch (_) { return false; }
}

async function shell(e, req) {
  const c = await caches.open(V);
  const net = fetch(req).then(async res => {
    if (await isApp(res)) { try { await c.put("/", res.clone()); } catch (_) {} return res; }
    return res && res.ok ? res : null;
  }).catch(() => null);
  e.waitUntil(net);
  const hit = await c.match("/", { ignoreVary: true });
  if (!hit) return (await net) || new Response("Offline", { status: 503 });
  const res = await Promise.race([net, new Promise(r => setTimeout(() => r(null), WAIT))]);
  return res && (await isApp(res)) ? res : hit;
}
