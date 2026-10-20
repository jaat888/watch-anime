FROM python:3.12-slim

WORKDIR /app

# addon ki dependencies (requests + curl_cffi)
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# addon + uska data
COPY addon.py episodes_index.jsonl posters.json ./

# hosting platform PORT env deta hai; na de to 7700 chalega
ENV PORT=7700 \
    HOST_SUFFIX=""
EXPOSE 7700

CMD ["python3", "-u", "addon.py"]
