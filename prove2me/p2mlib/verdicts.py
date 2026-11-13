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
  unproved_imports  "Imported platform theorems must be Proved at submission time": a bundle imports a statement
                 that is live but not Proved (our proof only sketch-accepted). Waits; sent again once Proved.
  dependency_oom "Lean exited with code 137" while building the imports ("Failed to compile modules") or the
                 solution itself (ERROR "Failed to compile solution module: Failed to compile module <job>: ... code
                 137"; q153 2026-11-06: a 49 s piece importing 586 MB, killed after 138 s): out of memory. Before
                 that, FAILED "Failed to compile modules <imports>: ... Lean exited with code 137": the
                 worker was killed (out of memory) building the item's imported bundles, many heavy
                 ones in parallel. Unchanged retries failed alike (Eilenberg–Ganea 2026-10-25), but
                 on PlanarPacking (q152) siblings with the same import closure published: retried
                 DEPENDENCY_OOM_CAP times, then move the heavy proofs out of the bundles (publish
                 them as statements).
  platform_block a permanent refusal by the platform that no retry and no change to the item cures: "Source too
                 large for import parser: N bytes (max 1048576)", the import parser's 1 MiB cap on each *imported*
                 source (q361 2026-11-13: every item importing the 1,425,670-byte Def_EditApproximation). Stops at once;
                 ask the admins. Not the token scanner's cap on the submitted file itself, which is the file's
                 (compile_error: split it).
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
PIECE_OOM_CAP = 0        # earlier memory kills (hidden or dependency_oom, together) of a proof before it is split.
                         # dbenbenn 2026-11-09: a borderline piece (measured <= 7,100 MiB) is tried once, then split.
                         # q153 (2026-11-06): retries of proofs that had failed passed 1 in 20, so ten tries (a77afdc)
                         # mostly burned shared verifier time; 2026-11-08: all 106 pieces stopped after four kills
                         # peaked over ~7.1 GiB locally (accepted ones <= 7.1), so a smaller piece fits: split
UNPROVED_CAP = 20        # refusals for an imported statement not yet Proved before a person looks
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
_UNPROVED = re.compile(r"Imported platform theorems must be Proved")
_PLATFORM_BLOCK = re.compile(r"Source too large for import parser")
IMPORT_SOURCE_CAP = 1048576   # bytes: the import parser's cap on each imported source (q361)
_HEART = re.compile(r"\(deterministic\) timeout|maximum number of heartbeats")


def classify(status, error_message):
    m = error_message or ''
    if status in ('ACCEPTED', 'SKETCH_ACCEPTED', 'PUBLISHED'):
        return 'accepted'
    if status == 'WA':
        return 'wrong'
    if _HEART.search(m):
        return 'heartbeats'
    if _UNPROVED.search(m):
        return 'unproved_imports'
    if _PLATFORM_BLOCK.search(m):
        return 'platform_block'
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
    if item_kind == 'piece' and kind in ('hidden', 'dependency_oom'):
        # a proof's hidden cause has been an OOM kill whenever the tail showed (q153): either kind is one
        mem = history.get('hidden', 0) + history.get('dependency_oom', 0)
        return 'retry' if mem < PIECE_OOM_CAP else 'split'
    if kind == 'hidden':
        return 'retry' if n < HIDDEN_CAP else 'stop'
    if kind == 'heartbeats':
        return 'raise_heartbeats'
    if kind == 'unproved_imports':
        # a bundle sent while a statement it imports was live but not yet Proved (q153 2026-11-09, OAIQ098G362):
        # it waits in todo; splitrun.ready sends it again only once the platform says Proved
        return 'retry' if n < UNPROVED_CAP else 'stop'
    if kind == 'dependency_oom':
        return 'retry' if n < DEPENDENCY_OOM_CAP else 'stop'
    return 'stop'
