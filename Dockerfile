FROM python:3.12-slim

WORKDIR /app

# Dependencies (requests + curl_cffi)
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy every file of the repo, so a new file can never be left out again
COPY . .

# The hosting platform provides PORT; defaults to 7700
ENV PORT=7700 \
    DB_PATH=/data/data.db \
    HOST_SUFFIX=""
RUN mkdir -p /data
EXPOSE 7700

CMD ["python3", "-u", "addon.py"]
