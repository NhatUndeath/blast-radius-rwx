# Same base image (and digest) the organizers labeled every commit in.
FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90
COPY selector.py fixture_map.json /app/
RUN chmod 0755 /app && chmod 0644 /app/selector.py /app/fixture_map.json
CMD ["python", "-I", "/app/selector.py"]
