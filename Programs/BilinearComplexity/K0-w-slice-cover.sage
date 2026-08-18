# K0-w-slice-cover.sage -- exact rank-two boundary test for the W tensor.
#
# Compare the direct 2-term Brent equations with the mode-one slice-cover
# incidence.  The exact-rank test keeps all six full-rank dictionary charts.
# The unsaturated determinantal fixed fiber also retains a repeated-column
# point, but that point is not in the closure of the empty honest fixed-W
# incidence and does not itself certify border rank.  A border-rank statement
# requires a separate family in which the tensor varies toward W.
#
# This program uses exact rational polynomial arithmetic and prints one JSON
# object.  It writes no files.

import hashlib
import json
import time


def polynomial_digest(polys):
    payload = "\n".join(str(f) for f in polys).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def groebner_unit_stats(ideal, one):
    started = time.perf_counter()
    basis = list(ideal.groebner_basis())
    elapsed = time.perf_counter() - started
    return basis, {
        "basis_size": int(len(basis)),
        "max_degree": int(max((f.total_degree() for f in basis), default=0)),
        "seconds": float(elapsed),
        "unit": bool(any(f == one for f in basis)),
    }


# W = e_100 + e_010 + e_001 in row-major tensor coordinates.
def w_entry(i, j, l):
    return QQ(1) if (i, j, l) in ((1, 0, 0), (0, 1, 0), (0, 0, 1)) else QQ(0)


# ---------------------------------------------------------------------------
# Baseline: direct Brent equations for two triads.
# ---------------------------------------------------------------------------
direct_names = (
    ["u%s%s" % (s, i) for s in range(2) for i in range(2)]
    + ["v%s%s" % (s, j) for s in range(2) for j in range(2)]
    + ["w%s%s" % (s, l) for s in range(2) for l in range(2)]
)
R = PolynomialRing(QQ, names=direct_names, order="degrevlex")
rg = R.gens_dict()
u = [[rg["u%s%s" % (s, i)] for i in range(2)] for s in range(2)]
v = [[rg["v%s%s" % (s, j)] for j in range(2)] for s in range(2)]
w = [[rg["w%s%s" % (s, l)] for l in range(2)] for s in range(2)]
direct_equations = [
    sum(u[s][i] * v[s][j] * w[s][l] for s in range(2)) - w_entry(i, j, l)
    for i in range(2) for j in range(2) for l in range(2)
]
direct_ideal = R.ideal(direct_equations)
direct_basis, direct_stats = groebner_unit_stats(direct_ideal, R.one())
assert direct_stats["unit"], "the direct equations incorrectly admit rank two"


# ---------------------------------------------------------------------------
# Slice cover: two rank-one 2x2 matrices m_0,m_1 must span both W slices.
#
# Slice columns in coordinate order (00,01,10,11):
#   A = W(0,-,-) = (0,1,1,0)
#   B = W(1,-,-) = (1,0,0,0).
# The unsaturated determinantal equations are the 3x3 minors of
# [m_0 m_1 A B].  Honest coverage additionally requires rank[m_0 m_1] = 2,
# covered by all nonzero 2x2-minor charts z*delta=1.  Because those charts are
# empty for fixed W, the unsaturated fiber is not the closure of the honest
# fixed-W incidence.
# ---------------------------------------------------------------------------
slice_names = (
    ["p%s%s" % (s, j) for s in range(2) for j in range(2)]
    + ["q%s%s" % (s, l) for s in range(2) for l in range(2)]
    + ["z"]
)
S = PolynomialRing(QQ, names=slice_names, order="degrevlex")
sg = S.gens_dict()
p = [[sg["p%s%s" % (s, j)] for j in range(2)] for s in range(2)]
q = [[sg["q%s%s" % (s, l)] for l in range(2)] for s in range(2)]
z = sg["z"]
pairs = [(0, 0), (0, 1), (1, 0), (1, 1)]
m = [[p[s][j] * q[s][l] for j, l in pairs] for s in range(2)]
A = [S(0), S(1), S(1), S(0)]
B = [S(1), S(0), S(0), S(0)]
combined = matrix(S, [[m[0][row], m[1][row], A[row], B[row]] for row in range(4)])
closure_equations = sorted(set(f for f in combined.minors(3) if f != 0), key=str)
closure_ideal = S.ideal(closure_equations)
closure_basis = list(closure_ideal.groebner_basis())
closure_unit = any(f == S.one() for f in closure_basis)
assert not closure_unit, "the unsaturated fixed fiber should retain its rank-drop point"

dictionary = matrix(S, [[m[0][row], m[1][row]] for row in range(4)])
rank_minors = sorted(set(f for f in dictionary.minors(2) if f != 0), key=str)
assert len(rank_minors) > 0

# The collision m_0=m_1=B lies on the unsaturated determinantal equations but
# on no full-rank chart.  It is the fixed fiber's dependent-point rank-drop
# witness, not a limit of honest covers of fixed W.  The same collision occurs
# in the separate universal varying-tensor degeneration toward W.
boundary_values = {
    p[0][0]: S(1), p[0][1]: S(0), q[0][0]: S(1), q[0][1]: S(0),
    p[1][0]: S(1), p[1][1]: S(0), q[1][0]: S(1), q[1][1]: S(0),
    z: S(0),
}
assert all(f.subs(boundary_values) == 0 for f in closure_equations)
assert all(delta.subs(boundary_values) == 0 for delta in rank_minors)

chart_stats = []
for chart, delta in enumerate(rank_minors):
    chart_ideal = S.ideal(closure_equations + [z * delta - 1])
    chart_basis, stats = groebner_unit_stats(chart_ideal, S.one())
    stats.update({
        "chart": int(chart),
        "minor": str(delta),
        "equation_digest": polynomial_digest(closure_equations + [z * delta - 1]),
    })
    assert stats["unit"], "a full-rank slice chart incorrectly survives"
    chart_stats.append(stats)
assert all(stats["unit"] for stats in chart_stats)


# ---------------------------------------------------------------------------
# Exact residual in intrinsic coordinates on the W slice plane.
#
# Every matrix alpha*A + beta*B is [[beta,alpha],[alpha,0]], whose determinant
# is -alpha^2.  Two such rank-one matrices would need
# D = alpha_0*beta_1-alpha_1*beta_0 != 0.  The explicit identity below proves
# that <alpha_0^2, alpha_1^2, z*D-1> is the unit ideal.
# ---------------------------------------------------------------------------
P = PolynomialRing(QQ, names=["alpha0", "beta0", "alpha1", "beta1", "z"],
                   order="degrevlex")
alpha0, beta0, alpha1, beta1, zz = P.gens()
D = alpha0 * beta1 - alpha1 * beta0
f0 = alpha0^2
f1 = alpha1^2
f2 = zz * D - 1
h0 = zz^3 * (alpha0 * beta1^3 - 3 * alpha1 * beta1^2 * beta0)
h1 = zz^3 * (3 * alpha0 * beta1 * beta0^2 - alpha1 * beta0^3)
h2 = -((zz * D)^2 + zz * D + 1)
certificate_value = h0 * f0 + h1 * f1 + h2 * f2
assert certificate_value == 1, "explicit residual Nullstellensatz certificate failed"

# The unsaturated intrinsic residual is nonreduced: alpha_0 is not in the
# ideal generated by alpha_0^2 and alpha_1^2, although its square is.
# Set-theoretically its only rank-one direction in each factor is alpha=0,
# namely B.  This is not the closure of the empty localized residual.
closed_residual = P.ideal([f0, f1])
assert closed_residual.reduce(alpha0) != 0
assert closed_residual.reduce(alpha0^2) == 0

result = {
    "benchmark": "W tensor, honest rank <= 2",
    "field": "QQ / algebraic closure certificate",
    "direct": {
        "variables": int(R.ngens()),
        "equations": int(len(direct_equations)),
        "equation_digest": polynomial_digest(direct_equations),
        **direct_stats,
    },
    "slice": {
        "base_variables_without_chart_inverse": int(8),
        "variables_with_chart_inverse": int(S.ngens()),
        # The closure_* keys are retained to identify the executed artifact.
        # They denote the unsaturated determinantal compactification/fixed
        # fiber, not the closure of the honest fixed-W incidence.
        "closure_equations": int(len(closure_equations)),
        "closure_equation_digest": polynomial_digest(closure_equations),
        "closure_unit": bool(closure_unit),
        "rank_charts": int(len(rank_minors)),
        "all_rank_charts_empty": bool(all(stats["unit"] for stats in chart_stats)),
        "charts": chart_stats,
    },
    "intrinsic_residual": {
        "variables_with_inverse": int(P.ngens()),
        "equations": int(3),
        "certificate_verified": bool(certificate_value == 1),
        "certificate_coefficients": [str(h0), str(h1), str(h2)],
        "nonreduced_closed_residual": True,
        "rank_one_support": "alpha0=alpha1=0 (the repeated B direction)",
    },
}
print(json.dumps(result, sort_keys=True))
