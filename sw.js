/* mollad_jaat service worker.
   It keeps NO copy of the site any more: when the server is down the site must say so, not open from an old
   copy and then fail on every video.  It only removes the old saved copies (mj-shell-v4/v5) and lets every
   request go straight to the network.  (Kept as a file so installed apps and old pages update cleanly.) */
const V = "mj-shell-v6";

self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", e => e.waitUntil((async () => {
  for (const k of await caches.keys()) await caches.delete(k);
  await self.clients.claim();
})()));
