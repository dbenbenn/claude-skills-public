"""What a prove2.me verdict or publish result means, and what to do next.

`classify(status, error_message)` -> one of
  accepted       ACCEPTED, SKETCH_ACCEPTED, PUBLISHED
  transient      the platform, not the item: cold workers loading imported bundles ("Failed to
                 materialize the target's dependencies", publish-side "Internal error while
                 publishing: Module compilation timed out"), database drops ("DB error ...
                 ConnectionTerminated"), "Import parser timed out", network errors. Retry.
  own_timeout    the item's own compile is too slow ("Verification timed out", "Failed to compile
                 solution module: Module compilation timed out", publish FAILED "Compilation timed
                 out"). Retrying is a lottery (an 84 s piece passed after 129 tries); split instead.
  heartbeats     a deterministic heartbeat timeout: raise maxHeartbeats on that declaration.
  compile_error  CE, or FAILED "... does not compile" for a real reason: fix the file.
  wrong          WA: the solution does not prove the published statement (a target renamed wrong,
                 a signature mismatch, an import clash with the statement's own imports).
  refused        anything else.

`decide(kind, history)` -> done | retry | give_up | split | raise_heartbeats | stop, where history
counts earlier results of this item by kind. Erdős 3 (2026-10-08..16) treated every ERROR as
transient and retried one piece 740 times; these rules are why that cannot recur.
"""
import re

OWN_TIMEOUT_CAP = 2      # own timeouts before splitting
TRANSIENT_CAP = 30       # transient failures before giving up for this run (cold-cache p90 was 10)

_TRANSIENT = re.compile(
    r"Failed to materialize the target's dependencies|Failed to resolve platform imports|"
    r"Internal error while publishing|DB error looking up import|ConnectionTerminated|"
    r"Import parser timed out|urlopen error|Connection(?:Reset|Refused)?Error|Temporary failure|"
    r"Network is unreachable|No route to host")
_OWN = re.compile(r"Verification timed out|Failed to compile solution module|^Compilation timed out")
_HEART = re.compile(r"\(deterministic\) timeout|maximum number of heartbeats")


def classify(status, error_message):
    m = error_message or ''
    if status in ('ACCEPTED', 'SKETCH_ACCEPTED', 'PUBLISHED'):
        return 'accepted'
    if status == 'WA':
        return 'wrong'
    if _HEART.search(m):
        return 'heartbeats'
    # a database drop or import-parser timeout inside a FAILED is still the platform's fault
    if _TRANSIENT.search(m):
        return 'transient'
    if _OWN.search(m):
        return 'own_timeout'
    if status == 'CE' or 'does not compile' in m or 'Compile error' in m:
        return 'compile_error'
    return 'refused'


def decide(kind, history):
    """history: {kind: count of earlier results of this item}"""
    n = history.get(kind, 0)
    if kind == 'accepted':
        return 'done'
    if kind == 'transient':
        return 'retry' if n < TRANSIENT_CAP else 'give_up'
    if kind == 'own_timeout':
        return 'retry' if n < OWN_TIMEOUT_CAP else 'split'
    if kind == 'heartbeats':
        return 'raise_heartbeats'
    return 'stop'
