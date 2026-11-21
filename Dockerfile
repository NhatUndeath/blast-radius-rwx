# Same base image (and digest) the organizers labeled every commit in.
FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90
# Pinned sqlglot sources (eb11aec4be8cb2122afe713a4816662c3f0fb2fa, *.py only) used to parse the changed files.
COPY sqlglot_src.tar.gz /tmp/sqlglot_src.tar.gz
RUN mkdir -p /opt/sqlglot && tar -xzf /tmp/sqlglot_src.tar.gz -C /opt/sqlglot && rm /tmp/sqlglot_src.tar.gz \
    && python -m compileall -q /opt/sqlglot/sqlglot     && chmod -R a+rX /opt/sqlglot
COPY selector.py replay_core.py cov_map.json.gz struct_map.json fixture_map.json replay_map.json.gz /app/
RUN chmod 0755 /app && chmod 0644 /app/*
ENV SQLGLOT_SRC=/opt/sqlglot PYTHONDONTWRITEBYTECODE=1
CMD ["python", "-I", "/app/selector.py"]
