const V = 'cards-v9';
const FILES = ['./', 'index.html', 'style.css', 'app.js', 'manifest.webmanifest', 'icon-192.png', 'icon-512.png', 'apple-touch-icon.png', 'lib/pdf.min.js', 'lib/pdf.worker.min.js'];
self.addEventListener('install', e => { e.waitUntil(caches.open(V).then(c => c.addAll(FILES.map(f => new Request(f, { cache: 'reload' })))).then(() => self.skipWaiting())); });
self.addEventListener('activate', e => { e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== V).map(k => caches.delete(k)))).then(() => self.clients.claim())); });
// Cache first: open instantly from the saved copy (a flaky or captive network, e.g. in-flight Wi-Fi, can hang a
// network-first request forever). Refresh the saved copy in the background, so an update shows on the next launch.
self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET' || new URL(req.url).origin !== location.origin) return;
  e.respondWith((async () => {
    const cache = await caches.open(V);
    const hit = await cache.match(req, { ignoreSearch: true });
    const refresh = fetch(req).then(r => { if (r && r.ok) cache.put(req, r.clone()); return r; }).catch(() => null);
    if (hit) { e.waitUntil(refresh); return hit; }
    return (await refresh) || new Response('Offline and not saved yet. Open the app once while online.', { status: 503 });
  })());
});
