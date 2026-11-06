"""What a prove2.me verdict or publish result means, and what to do next.

`classify(status, error_message)` -> one of
  accepted       ACCEPTED, SKETCH_ACCEPTED, PUBLISHED
  transient      the platform, not the item: cold workers loading imported bundles ("Failed to
                 materialize the target's dependencies", publish-side "Internal error while
                 publishing: Module compilation timed out"), database drops ("DB error ...
                 ConnectionTerminated"), "Import parser timed out", the lexer's "Token scanner timed out"
                 on small statements under load (oaiq-089: a reset republished all nine), network
                 errors. Retry.
  own_timeout    the item's own compile is too slow ("Verification timed out", "Failed to compile
                 solution module: Module compilation timed out", publish FAILED "Compilation timed
                 out"). Retrying is a lottery (an 84 s piece passed after 129 tries); split instead.
  hidden         ERROR "Failed to compile solution module: Failed to compile module <job>: <build
                 output>" with no error in what is shown: the platform cuts error_message at about
                 4 KB, and the replay warnings of the imported statements ("declaration uses
                 `sorry`", one per stub) fill it, so the cause is cut off. Not a timeout (those say
                 "timed out"): q153 PlanarPacking 2026-11-06, four pieces of 49-65 s locally
                 (137 MB import closure) failed so 22 times and were taken for timeouts. Retried
                 HIDDEN_CAP times, then a person looks.
  heartbeats     a deterministic heartbeat timeout: raise maxHeartbeats on that declaration.
  dependency_oom "Lean exited with code 137" while building the imports ("Failed to compile modules") or the
                 solution itself (ERROR "Failed to compile solution module: Failed to compile module <job>: ... code
                 137"; q153 2026-11-06: a 49 s piece importing 586 MB, killed after 138 s): out of memory. Before
                 that, FAILED "Failed to compile modules <imports>: ... Lean exited with code 137": the
                 worker was killed (out of memory) building the item's imported bundles, many heavy
                 ones in parallel. Unchanged retries failed alike (Eilenberg–Ganea 2026-10-25), but
                 on PlanarPacking (q152) siblings with the same import closure published: retried
                 DEPENDENCY_OOM_CAP times, then move the heavy proofs out of the bundles (publish
                 them as statements).
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
HIDDEN_CAP = 2           # hidden-cause solution compile failures before stopping for a person
DEPENDENCY_OOM_CAP = 3   # dependency_oom results before stopping for a person (q152)
PIECE_OOM_CAP = 3        # the same for a proof. q153 (2026-11-06): first tries of proofs importing 300-600 MB passed
                         # ~55%, but retries of ones that had failed passed 1 in 20: a proof over the worker's memory
                         # fails again, so ten tries (a77afdc) mostly burned shared verifier time
TRANSIENT_CAP = 30       # transient failures before giving up for this run (cold-cache p90 was 10)

_TRANSIENT = re.compile(
    r"Failed to materialize the target's dependencies|Failed to resolve platform imports|"
    r"Internal error while publishing|DB error looking up import|ConnectionTerminated|"
    r"Import parser timed out|Token scanner timed out|urlopen error|Connection(?:Reset|Refused)?Error|Temporary failure|"
    r"Network is unreachable|No route to host|"
    # a refused post the platform answered with a server error (q151: "500 ... Verification service
    # error: could not store the proof file: Gateway Timeout" stopped nine pieces)
    r"Verification service error|Gateway Time-?out|Bad Gateway|Service Unavailable|__error\W+5\d\d\b")
_OWN = re.compile(r"Verification timed out|Failed to compile solution module: Module compilation timed out|"
                  r"^Compilation timed out")
_SOLUTION_BUILD = re.compile(r"^Failed to compile solution module: Failed to compile module ")
_ERROR_LINE = re.compile(r"(?m)^(error: |\u2716 )")
_DEP_OOM = re.compile(r"Failed to compile modules? .*exited with code 137", re.S)
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
    if _DEP_OOM.search(m):
        return 'dependency_oom'
    if _SOLUTION_BUILD.search(m):
        return 'compile_error' if _ERROR_LINE.search(m) else 'hidden'
    if status == 'CE' or 'does not compile' in m or 'Compile error' in m:
        return 'compile_error'
    return 'refused'


def decide(kind, history, item_kind=None):
    """history: {kind: count of earlier results of this item}; item_kind 'piece' for a proof."""
    n = history.get(kind, 0)
    if kind == 'accepted':
        return 'done'
    if kind == 'transient':
        return 'retry' if n < TRANSIENT_CAP else 'give_up'
    if kind == 'own_timeout':
        return 'retry' if n < OWN_TIMEOUT_CAP else 'split'
    if kind == 'hidden':
        # a proof's hidden cause has been an OOM kill whenever the tail showed (q153): retried like one
        return 'retry' if n < (PIECE_OOM_CAP if item_kind == 'piece' else HIDDEN_CAP) else 'stop'
    if kind == 'heartbeats':
        return 'raise_heartbeats'
    if kind == 'dependency_oom':
        return 'retry' if n < (PIECE_OOM_CAP if item_kind == 'piece' else DEPENDENCY_OOM_CAP) else 'stop'
    return 'stop'
