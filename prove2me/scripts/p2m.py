#!/usr/bin/env python3
import json,os,sys,time,urllib.request,urllib.error
def _workspace():
    """The prove2.me Lean workspace: $P2M_WORKSPACE, else the first of the known locations."""
    for p in [os.environ.get('P2M_WORKSPACE'), '~/claude/prove2me_workspace', '~/prove2me_workspace']:
        if p and os.path.isdir(os.path.expanduser(p)):
            return os.path.expanduser(p)
    raise SystemExit('prove2.me workspace not found; set P2M_WORKSPACE')
WS=_workspace()
_key=json.load(open(WS+"/credentials.json"))["api_key"]
_T=None
def token(refresh=False):
    """Access tokens last an hour; call() refreshes on a 401, so a long watch does not go blind."""
    global _T
    if _T is None or refresh:
        _T=json.load(urllib.request.urlopen(urllib.request.Request(
          "https://prove2.me/api/v1/agent/refresh",data=json.dumps({"api_key":_key}).encode(),
          headers={"Content-Type":"application/json"})))["access_token"]
    return _T
def _no_docstring(b):
    """A published statement carries no comment of any kind: `formal_statement` and `preamble`
    freeze at publish, and the blind read-back never sees comments, so one is both unauditable
    and unfixable. Detection uses the stager's literal-aware strip(), so `"a--b"` is not a
    comment. Definition bundles are untouched — their code travels in `definition`, not here.
    Set P2M_ALLOW_DOCSTRING=1 to override deliberately."""
    if os.environ.get("P2M_ALLOW_DOCSTRING") == "1": return
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from stage_auditor import strip
    for part in ([b] if isinstance(b,dict) else []) + (b.get("problems") or [] if isinstance(b,dict) else []):
        for field in ("formal_statement", "preamble"):
            fs = part.get(field) if isinstance(part,dict) else None
            if fs and ("--" in fs or "/-" in fs) and strip(fs).split() != fs.split():
                raise SystemExit("refusing: %s carries a comment, which freezes at publish and is "
                                 "never read back. Put it in natural_language_statement, or set "
                                 "P2M_ALLOW_DOCSTRING=1." % field)
def call(m,p,b=None):
    url="https://prove2.me/api/v1"+p
    if m in ("POST","PATCH") and isinstance(b,dict): _no_docstring(b)
    assert url.startswith("https://prove2.me/api/v1")
    d=json.dumps(b).encode() if b is not None else None
    h={"Authorization":"Bearer "+token()}
    if d: h["Content-Type"]="application/json"
    refreshed=False
    for a in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url,data=d,headers=h,method=m),timeout=180) as f:
                return json.loads(f.read().decode() or "{}")
        except urllib.error.HTTPError as e:
            if e.code>=500 or e.code==429: time.sleep(6*(a+1)); continue
            if e.code==401 and not refreshed:
                refreshed=True; h["Authorization"]="Bearer "+token(refresh=True); continue
            return {"__error":"%d %s"%(e.code,e.read().decode()[:400])}
        except Exception as e:
            time.sleep(4*(a+1))
    return {"__error":"retries exhausted"}
if __name__=="__main__":
    m=sys.argv[1]; p=sys.argv[2]
    b=json.loads(sys.argv[3]) if len(sys.argv)>3 else None
    print(json.dumps(call(m,p,b),indent=1))
