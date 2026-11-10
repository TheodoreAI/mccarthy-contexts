#!/usr/bin/env python3
"""Submit the private draft problem and verified proof for
`TranscendenceTower.ExternalGroundingPlatform.necessary_external_grounding`
to Prove2Me without ever logging credentials or tokens.
"""

import json
import pathlib
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

BASE_URL = "https://prove2.me/api/v1"
WIN_CFG = pathlib.Path("/mnt/c/Users/mateo/.config/prove2me")
WSL_CFG = pathlib.Path("/home/mateoestrada/.config/prove2me")
ROOT = pathlib.Path("/home/mateoestrada/mccarthy-contexts")
PAYLOAD_PATH = ROOT / "build" / "payloads" / "payload_thm_external_grounding.json"
SOL_PATH = ROOT / "Solutions" / "Sol_necessary_external_grounding.lean"
EXPL_PATH = ROOT / "build" / "payloads" / "Sol_necessary_external_grounding.expl.md"


def read_clean_secret(path: pathlib.Path, prefix: str) -> str:
    raw = path.read_bytes()
    for enc in ("utf-8-sig", "utf-16", "utf-8"):
        try:
            cand = raw.decode(enc).strip()
            if cand.startswith(prefix):
                return cand
        except Exception:
            continue
    raise RuntimeError(f"Could not decode token/key from {path.name}")


def get_access_token() -> str:
    tok_path = WIN_CFG / "access_token"
    if tok_path.exists():
        try:
            tok = read_clean_secret(tok_path, "eyJ")
            # Test if current access_token is valid via GET /me
            req = urllib.request.Request(
                f"{BASE_URL}/me",
                headers={
                    "Authorization": f"Bearer {tok}",
                    "User-Agent": "prove2me-client/1.0",
                },
                method="GET",
            )
            with urllib.request.urlopen(req) as resp:
                if resp.status == 200:
                    WSL_CFG.mkdir(parents=True, exist_ok=True)
                    (WSL_CFG / "access_token").write_text(tok, encoding="utf-8")
                    return tok
        except Exception:
            pass

    api_key = read_clean_secret(WIN_CFG / "api_key", "p2m_")
    req = urllib.request.Request(
        f"{BASE_URL}/agent/refresh",
        data=b"",
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Length": "0",
            "User-Agent": "prove2me-client/1.0",
        },
        method="POST",
    )
    with urllib.request.urlopen(req) as resp:
        body = json.loads(resp.read().decode("utf-8"))
    token = body["access_token"].strip()
    WIN_CFG.mkdir(parents=True, exist_ok=True)
    WSL_CFG.mkdir(parents=True, exist_ok=True)
    (WIN_CFG / "access_token").write_text(token, encoding="utf-8")
    (WSL_CFG / "access_token").write_text(token, encoding="utf-8")
    return token


def api_json(method: str, path: str, token: str, payload=None) -> dict:
    data = None
    headers = {
        "Authorization": f"Bearer {token}",
        "User-Agent": "prove2me-client/1.0",
    }
    if payload is not None:
        data = (
            payload
            if isinstance(payload, bytes)
            else json.dumps(payload, ensure_ascii=False).encode("utf-8")
        )
        headers["Content-Type"] = "application/json; charset=utf-8"
    req = urllib.request.Request(
        f"{BASE_URL}{path}", data=data, headers=headers, method=method
    )
    try:
        with urllib.request.urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {e.code} on {method} {path}: {err_body}") from None


def submit_multipart_verify(
    token: str, theorem_id: str, sol_bytes: bytes, explanation: str
) -> dict:
    boundary = f"----Prove2MeBoundary{uuid.uuid4().hex}"
    parts = []

    def add_field(name: str, value: str):
        parts.append(
            f"--{boundary}\r\n"
            f'Content-Disposition: form-data; name="{name}"\r\n\r\n'
            f"{value}\r\n".encode("utf-8")
        )

    add_field("theorem_id", theorem_id)
    add_field("explanation", explanation)

    parts.append(
        (
            f"--{boundary}\r\n"
            f'Content-Disposition: form-data; name="file"; filename="Sol_necessary_external_grounding.lean"\r\n'
            f"Content-Type: text/plain; charset=utf-8\r\n\r\n"
        ).encode("utf-8")
        + sol_bytes
        + b"\r\n"
    )
    parts.append(f"--{boundary}--\r\n".encode("utf-8"))
    body = b"".join(parts)

    req = urllib.request.Request(
        f"{BASE_URL}/verify",
        data=body,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": f"multipart/form-data; boundary={boundary}",
            "User-Agent": "prove2me-client/1.0",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {e.code} on POST /verify: {err_body}") from None


def main():
    token = get_access_token()
    print("[1/4] Refreshed access token silently.")

    # Check if theorem already exists in private theorems
    q = urllib.parse.quote("necessary_external_grounding")
    existing = api_json(
        "GET", f"/theorems?q={q}&include_private=true&limit=20", token
    )
    theorem_id = None
    for thm in existing.get("theorems", []):
        if (
            thm.get("theorem_name")
            == "TranscendenceTower.ExternalGroundingPlatform.necessary_external_grounding"
        ):
            theorem_id = thm["theorem_id"]
            print(
                f"[2/4] Found existing private theorem: theorem_id={theorem_id}, "
                f"status={thm.get('status')}, visibility={thm.get('visibility')}"
            )
            break

    if not theorem_id:
        print("[2/4] Submitting private problem payload to /submit-problem...")
        sub = api_json("POST", "/submit-problem", token, PAYLOAD_PATH.read_bytes())
        print("  submit-problem response:", json.dumps(sub, indent=2))
        jobs = sub.get("jobs", [])
        if not jobs:
            raise RuntimeError(f"No jobs returned: {sub}")
        job_id = jobs[0]["job_id"]
        print(f"  Polling publish job {job_id}...")
        while True:
            time.sleep(5)
            job = api_json("GET", f"/publish-jobs/{job_id}", token)
            status = job.get("status")
            print(f"    job status: {status}")
            if status == "PUBLISHED":
                theorem_id = job["theorem_id"]
                print(
                    f"  PUBLISHED: theorem_id={theorem_id}, visibility={job.get('visibility')}"
                )
                break
            elif status in ("FAILED", "ERROR"):
                raise RuntimeError(
                    f"Publish job {status}: {job.get('error_message')}"
                )

    print(f"[3/4] Submitting proof Sol_necessary_external_grounding.lean for theorem_id={theorem_id}...")
    sol_bytes = SOL_PATH.read_bytes()
    expl_text = EXPL_PATH.read_text(encoding="utf-8")
    ver_sub = submit_multipart_verify(token, theorem_id, sol_bytes, expl_text)
    submission_id = ver_sub["submission_id"]
    print(f"  submission_id={submission_id}, initial status={ver_sub.get('status')}")

    print(f"[4/4] Polling GET /verify?submission_id={submission_id}...")
    while True:
        time.sleep(5)
        res = api_json("GET", f"/verify?submission_id={submission_id}", token)
        vstatus = res.get("status")
        print(f"    verify status: {vstatus}")
        if vstatus not in ("PENDING", "RUNNING", "QUEUED"):
            print(
                json.dumps(
                    {
                        "submission_id": res.get("id", submission_id),
                        "theorem_id": theorem_id,
                        "status": vstatus,
                        "error_message": res.get("error_message"),
                        "compiler_output": res.get("compiler_output"),
                    },
                    indent=2,
                )
            )
            break


if __name__ == "__main__":
    main()
