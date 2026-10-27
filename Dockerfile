FROM python:3.12-slim

WORKDIR /app

# Dependencies (requests + curl_cffi)
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy every file of the repo, so a new file can never be left out again
COPY . .

# The hosting platform provides PORT; defaults to 7700
# MALLOC_ARENA_MAX=1: glibc gives every thread its own memory arena, which makes a
# threaded Python server grow past 1 GB for no reason.  1 arena = far less RAM.
ENV PORT=7700 \
    DB_PATH=/data/data.db \
    HOST_SUFFIX="" \
    MALLOC_ARENA_MAX=1 \
    MALLOC_TRIM_THRESHOLD_=131072 \
    PYTHONDONTWRITEBYTECODE=1
RUN mkdir -p /data
EXPOSE 7700

CMD ["python3", "-u", "addon.py"]
