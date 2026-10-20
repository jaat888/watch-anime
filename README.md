# RareToons API

Python server (Stremio addon) jo anime/toons ke stream links deta hai.
Aage chalke website isi API ko call karegi (CORS already open hai).

## Endpoints
- `GET /manifest.json`                      - addon info
- `GET /meta/series/raretoons2:<slug>.json` - show + episodes list
- `GET /stream/<type>/<id>.json`            - episode ke stream links
- `GET /mq/...`                             - video proxy (HLS)

## Local chalana
    pip install -r requirements.txt
    python3 addon.py 7700
    # browser: http://localhost:7700/manifest.json

## Docker
    docker build -t raretoons .
    docker run -p 7700:7700 raretoons

## Naye shows add karna (laptop pe)
    pip install -r requirements-crawler.txt
    python3 refresh_index.py
    git add -A && git commit -m "update index" && git push
(Iske liye `streams.json` chahiye, wo repo mein nahi hai.)

## Files
- addon.py, episodes_index.jsonl, posters.json, requirements.txt : server
- Dockerfile, .dockerignore, Procfile                            : deploy
- crawler.py, parse_hubs.py, refresh_index.py                    : data update tools
