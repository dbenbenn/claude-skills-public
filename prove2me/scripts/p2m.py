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
def token():
    global _T
    if _T is None:
        _T=json.load(urllib.request.urlopen(urllib.request.Request(
          "https://prove2.me/api/v1/agent/refresh",data=json.dumps({"api_key":_key}).encode(),
          headers={"Content-Type":"application/json"})))["access_token"]
    return _T
def call(m,p,b=None):
    url="https://prove2.me/api/v1"+p
    assert url.startswith("https://prove2.me/api/v1")
    d=json.dumps(b).encode() if b is not None else None
    h={"Authorization":"Bearer "+token()}
    if d: h["Content-Type"]="application/json"
    for a in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url,data=d,headers=h,method=m),timeout=180) as f:
                return json.loads(f.read().decode() or "{}")
        except urllib.error.HTTPError as e:
            if e.code>=500 or e.code==429: time.sleep(6*(a+1)); continue
            return {"__error":"%d %s"%(e.code,e.read().decode()[:400])}
        except Exception as e:
            time.sleep(4*(a+1))
    return {"__error":"retries exhausted"}
if __name__=="__main__":
    m=sys.argv[1]; p=sys.argv[2]
    b=json.loads(sys.argv[3]) if len(sys.argv)>3 else None
    print(json.dumps(call(m,p,b),indent=1))
