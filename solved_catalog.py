"""Curated catalog of classical information-theory theorems proved in Lean 4.

Consumed by build.py to generate "Solved Problems in Information Theory: Lean Proofs"
(site/solved/index.html and site/solved/<id>.html) and to automatically compute
bidirectional links between solved theorems and open problems.

Every `lean_decls` entry is `(repo_relative_lean_path, declaration_name)` and is
verified against the actual `.lean` files at site build time. Every `related_open`
entry is a problem id in `problems/<id>.md` and is also verified at build time.
"""

SOLVED_CATEGORY_LABELS = {
    "ch2-entropy": "Ch. 2 · Entropy, Divergence & Inequalities",
    "ch3-4-aep": "Ch. 3–4 · AEP, Typicality & Entropy Rates",
    "ch5-compression": "Ch. 5 · Data Compression & Source Coding",
    "ch7-channel": "Ch. 7 · Channel Capacity & Error Exponents",
    "ch8-9-gaussian": "Ch. 8–9 · Differential Entropy & AWGN",
    "ch10-rate-distortion": "Ch. 10 · Rate–Distortion Theory",
    "ch11-types": "Ch. 11 · Method of Types & Statistics",
    "ch15-network": "Ch. 15 / EGK · Network Information Theory",
    "entropy-region": "Entropy Region & Non-Shannon Inequalities",
    "zero-error-coding": "Zero-Error & Classical Coding Bounds",
}

SOLVED_THEOREMS = [
    # ------------------------------------------------------------------ Ch. 2
    {
        "id": "gibbs-inequality",
        "title": "Gibbs' Inequality and Non-negativity of KL Divergence",
        "category": "ch2-entropy",
        "authors": "Josiah Willard Gibbs; Solomon Kullback and Richard Leibler",
        "year": "1951",
        "reference": "Cover & Thomas, Theorem 2.6.3; bridged to Mathlib.InformationTheory.klDiv",
        "tags": ["kl-divergence", "gibbs", "mathlib-bridge", "ch2"],
        "statement": (
            "For any two probability distributions $P, Q$ on a finite alphabet $\\mathcal{X}$ "
            "with $P \\ll Q$, the Kullback–Leibler divergence satisfies\n"
            "$$D(P \\| Q) = \\sum_{x \\in \\mathcal{X}} P(x) \\log_2 \\frac{P(x)}{Q(x)} \\ge 0,$$\n"
            "with equality $D(P \\| Q) = 0$ if and only if $P = Q$."
        ),
        "proof_notes": (
            "Proved by constructing an exact bridge from `InfoTheory.Core.ProbDist` to Mathlib's "
            "`PMF` and `MeasureTheory.Measure`, identifying `Real.log 2 * klDivergence P Q` with "
            "`(InformationTheory.klDiv (toMeasure P) (toMeasure Q)).toReal`, and inheriting both "
            "non-negativity and the strict equality characterization directly from Mathlib's "
            "`InformationTheory.klDiv`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/Mathlib.lean", "klDivergence_eq_toReal_klDiv"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "klDivergence_nonneg"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "klDivergence_eq_zero_iff"),
        ],
        "related_open": [
            "minimax-kl-large-alphabet",
            "ldp-minimax-kl-sharp",
            "sdpi-kl-vs-chisq-equality",
            "hypercontractivity-ribbon-discrete",
            "log-sobolev-hypercube-sharp",
        ],
    },
    {
        "id": "data-processing-inequality",
        "title": "Data Processing Inequality for Maps, Channels, and Mutual Information",
        "category": "ch2-entropy",
        "authors": "Claude E. Shannon; Imre Csiszár",
        "year": "1948",
        "reference": "Cover & Thomas, Theorem 2.8.1; bridged to Mathlib.InformationTheory.KullbackLeibler.DataProcessing",
        "tags": ["dpi", "markov-chains", "dmc", "mathlib-bridge", "ch2"],
        "statement": (
            "Processing data cannot increase relative entropy or mutual information:\n"
            "- For any deterministic map $f : \\mathcal{X} \\to \\mathcal{Y}$ and $P \\ll Q$, "
            "$D(f_* P \\| f_* Q) \\le D(P \\| Q)$.\n"
            "- For any discrete memoryless channel $W : \\mathcal{X} \\to \\mathcal{Y}$ and $P \\ll Q$, "
            "$D(WP \\| WQ) \\le D(P \\| Q)$.\n"
            "- For any Markov chain $X - Y - Z$ induced by a map or channel $W$, "
            "$I(X; Z) \\le I(X; Y)$."
        ),
        "proof_notes": (
            "Bridges `InfoTheory.Core.DMC` to Mathlib's Markov kernels (`ProbabilityTheory.Kernel`), "
            "pulls back `InformationTheory.klDiv_map_le` and `klDiv_comp_right_le`, and derives the "
            "mutual-information DPI by applying channel DPI to the lifted channel $\\mathrm{id} \\times W$ "
            "on $P_{XY}$ vs. $P_X \\times P_Y$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/Mathlib.lean", "klDivergence_map_le"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "klDivergence_channel_le"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "mutualInfo_map_right_le"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "mutualInfo_channel_right_le"),
        ],
        "related_open": [
            "sdpi-kl-vs-chisq-equality",
            "hypercontractivity-ribbon-discrete",
            "courtade-kumar",
            "courtade-kumar-qary",
            "li-medard-conjecture",
            "deletion-channel",
            "intrinsic-vs-secret-key-gap",
        ],
    },
    {
        "id": "max-entropy-and-conditioning",
        "title": "Maximum Entropy of Uniform Distributions & Conditioning Reduces Entropy",
        "category": "ch2-entropy",
        "authors": "Claude E. Shannon",
        "year": "1948",
        "reference": "Cover & Thomas, Theorems 2.6.4 & 2.6.5, Eq. 2.28 & 2.90",
        "tags": ["shannon-entropy", "mutual-information", "conditioning", "ch2"],
        "statement": (
            "For finite discrete random variables $X, Y$:\n"
            "$$0 \\le H(X) \\le \\log_2 |\\mathcal{X}|, \\qquad H(X) = \\log_2 |\\mathcal{X}| \\iff P_X = \\mathrm{Unif}(\\mathcal{X}),$$\n"
            "$$I(X; Y) = D(P_{XY} \\| P_X \\times P_Y) \\ge 0, \\qquad I(X; Y) = 0 \\iff P_{XY} = P_X \\times P_Y,$$\n"
            "and conditioning reduces entropy: $H(X \\mid Y) \\le H(X)$."
        ),
        "proof_notes": (
            "Derived directly from `klDivergence_nonneg` and `klDivergence_eq_zero_iff` via the "
            "identities $D(P \\| \\mathrm{Unif}) = \\log_2 |\\mathcal{X}| - H(P)$ and "
            "$I(X; Y) = D(P_{XY} \\| P_X \\times P_Y)$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/Mathlib.lean", "shannonEntropy_nonneg"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "shannonEntropy_le_log2_card"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "shannonEntropy_eq_log2_card_iff"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "mutualInfo_eq_klDivergence"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "mutualInfo_nonneg"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "mutualInfo_eq_zero_iff_indep"),
            ("lean/InfoTheory/Bridge/Mathlib.lean", "condEntropy_le_shannonEntropy"),
        ],
        "related_open": [
            "conditional-entropy-sharp-continuity",
            "entropic-doubling-constant",
            "graph-entropy-subadditivity",
        ],
    },
    {
        "id": "chain-rules-and-polymatroids",
        "title": "Chain Rules, Strong Subadditivity, and Shannon Polymatroid Inclusion",
        "category": "ch2-entropy",
        "authors": "Claude E. Shannon; Fujishige; Raymond W. Yeung",
        "year": "1978",
        "reference": "Cover & Thomas, §§2.2–2.6; Yeung, Ch. 13",
        "tags": ["chain-rule", "strong-subadditivity", "polymatroid", "shannon-inequalities", "ch2"],
        "statement": (
            "For any finite joint distributions:\n"
            "- Chain rule: $H(X, Y) = H(Y) + H(X \\mid Y)$ with $H(X \\mid Y) \\ge 0$ and $H(f(X)) \\le H(X)$.\n"
            "- Strong subadditivity: $I(X; Y \\mid Z) \\ge 0$, with equality iff $X - Z - Y$.\n"
            "- Every entropic vector and every almost-entropic vector is a polymatroid: "
            "$\\Gamma^*_n \\subseteq \\operatorname{cl}(\\Gamma^*_n) \\subseteq \\Gamma_n$."
        ),
        "proof_notes": (
            "Strong subadditivity is proved by identifying $I(X; Y \\mid Z) = D(P_{XYZ} \\| P_{XZ} P_{YZ} / P_Z)$ "
            "and invoking Gibbs' inequality. Submodularity of subset entropy vectors follows immediately "
            "by partitioning $S \\cup T$ into $(S \\setminus T, T \\setminus S, S \\cap T)$, and closure "
            "stability in `Known/EntropyRegion.lean` lifts this to $\\operatorname{cl}(\\Gamma^*_n) \\subseteq \\Gamma_n$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "shannonEntropy_chain_rule"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "shannonEntropy_map_le"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "condEntropy_nonneg"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "condMutualInfo_nonneg"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "condMutualInfo_eq_zero_iff"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "subsetEntropyVec_isPolymatroid"),
            ("lean/InfoTheory/Known/EntropyRegion.lean", "almostEntropic_isPolymatroid"),
        ],
        "related_open": [
            "entropy-region",
            "entropy-region-decidability",
            "linear-rank-entropy-region-n6",
            "secret-sharing-optimal-info-ratio",
            "graph-entropy-subadditivity",
        ],
    },
    {
        "id": "log-sum-and-convexity",
        "title": "Log-Sum Inequality, Convexity of KL Divergence, and Concavity of Entropy",
        "category": "ch2-entropy",
        "authors": "Imre Csiszár; Thomas M. Cover and Joy A. Thomas",
        "year": "1991",
        "reference": "Cover & Thomas, Theorems 2.7.1–2.7.3",
        "tags": ["log-sum", "convexity", "concavity", "ch2"],
        "statement": (
            "For nonnegative numbers $a_i, b_i \\ge 0$ with $b_i = 0 \\implies a_i = 0$,\n"
            "$$\\left(\\sum_i a_i\\right) \\log_2 \\frac{\\sum_i a_i}{\\sum_i b_i} \\le \\sum_i a_i \\log_2 \\frac{a_i}{b_i}.$$\n"
            "Consequently, $D(P \\| Q)$ is jointly convex in $(P, Q)$ (on $P \\ll Q$) and $H(P)$ is concave in $P$."
        ),
        "proof_notes": (
            "Derived from the non-negativity of Mathlib's `InformationTheory.klFun` and applied "
            "coordinatewise to convex mixtures `probMix t P₁ P₂`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "log_sum_inequality"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "klDivergence_convex"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "shannonEntropy_concave"),
        ],
        "related_open": [
            "conditional-entropy-sharp-continuity",
            "sdpi-kl-vs-chisq-equality",
            "hypercontractivity-ribbon-discrete",
            "mrs-gerber-general",
        ],
    },
    {
        "id": "fano-inequality",
        "title": "Fano's Inequality (Sharp and General Forms)",
        "category": "ch2-entropy",
        "authors": "Robert M. Fano",
        "year": "1952",
        "reference": "Cover & Thomas, Theorem 2.10.1; El Gamal & Kim, §2.1",
        "tags": ["fano", "converses", "ch2"],
        "statement": (
            "For any joint distribution $P_{XY}$ on $\\mathcal{X} \\times \\mathcal{Y}$ with "
            "$|\\mathcal{X}| \\ge 2$ and any estimator $g : \\mathcal{Y} \\to \\mathcal{X}$ with "
            "error probability $P_e = \\Pr[g(Y) \\ne X]$,\n"
            "$$H(X \\mid Y) \\le h(P_e) + P_e \\log_2(|\\mathcal{X}| - 1) \\le h(P_e) + P_e \\log_2 |\\mathcal{X}|.$$"
        ),
        "proof_notes": (
            "Proved cleanly in one shot via Gibbs' inequality (`klDivergence_nonneg`) against the "
            "isotropic-error reference distribution $Q(x, y) = (1 - P_e) P_Y(y)$ for $x = g(y)$ and "
            "$Q(x, y) = \\frac{P_e}{|\\mathcal{X}| - 1} P_Y(y)$ for $x \\ne g(y)$, handling the "
            "boundary cases $P_e \\in \\{0, 1\\}$ without auxiliary random variables."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "fano_inequality"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "fano_inequality_card"),
        ],
        "related_open": [
            "broadcast-channel",
            "dm-interference-channel-capacity",
            "relay-channel",
            "two-way-channel-capacity",
            "deletion-channel",
        ],
    },
    {
        "id": "csiszar-sum-identity",
        "title": "Csiszár's Sum Identity",
        "category": "ch2-entropy",
        "authors": "Imre Csiszár and János Körner",
        "year": "1978",
        "reference": "El Gamal & Kim, §2.3; Csiszár & Körner, Lemma 7",
        "tags": ["csiszar-sum", "network-it", "converses", "ch2"],
        "statement": (
            "For any blocklength $n$ and joint distribution on $(X^n, Y^n)$,\n"
            "$$\\sum_{i=1}^n I(X_i; Y_{i+1}^n \\mid X^{i-1}) = \\sum_{i=1}^n I(X^{i-1}; Y_i \\mid Y_{i+1}^n).$$"
        ),
        "proof_notes": (
            "Proved by expanding each conditional mutual information into subset entropies and "
            "telescoping via `prefixVec` and `suffixVec` equivalences."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "csiszar_sum_identity"),
        ],
        "related_open": [
            "broadcast-channel",
            "broadcast-channel-three-receivers",
            "marton-inner-bound-tightness",
            "binary-skew-symmetric-bc",
            "wiretap-channel-compound-secrecy",
            "wiretap-with-feedback-capacity",
            "secret-key-capacity-public-discussion",
            "intrinsic-vs-secret-key-gap",
        ],
    },

    # ------------------------------------------------------------------ Ch. 3–4
    {
        "id": "aep-weak-typicality",
        "title": "Asymptotic Equipartition Property (AEP) and Weak Typicality",
        "category": "ch3-4-aep",
        "authors": "Claude E. Shannon; Brockway McMillan; Leo Breiman",
        "year": "1948",
        "reference": "Cover & Thomas, Theorems 3.1.1 & 3.1.2",
        "tags": ["aep", "typical-set", "varentropy", "ch3"],
        "statement": (
            "For an i.i.d. finite source $X^n \\sim P^n$ and the weakly typical set "
            "$A_\\varepsilon^{(n)} = \\{x^n : 2^{-n(H(P)+\\varepsilon)} \\le P^n(x^n) \\le 2^{-n(H(P)-\\varepsilon)}\\}$:\n"
            "1. $1 - P^n(A_\\varepsilon^{(n)}) \\le \\frac{V(P)}{n \\varepsilon^2} \\to 0$ (explicit varentropy Chebyshev bound).\n"
            "2. $|A_\\varepsilon^{(n)}| \\le 2^{n(H(P) + \\varepsilon)}$ for all $n$.\n"
            "3. $|A_\\varepsilon^{(n)}| \\ge (1 - \\delta) 2^{n(H(P) - \\varepsilon)}$ for all sufficiently large $n$."
        ),
        "proof_notes": (
            "Proved completely via finite-sum independence of the centered surprisals "
            "$Z_i = -\\log_2 P(X_i) - H(P)$ with explicit variance `varentropy P`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "iidDist_prob_not_typical_le"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "aep_typical_prob_tendsto_one"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "weakTypicalSet_card_le"),
            ("lean/InfoTheory/Bridge/CoverThomas.lean", "weakTypicalSet_card_ge"),
        ],
        "related_open": [
            "non-asymptotic-lossy-dispersion",
            "universal-lossy-redundancy",
            "covert-communication-second-order",
        ],
    },
    {
        "id": "joint-aep-and-packing",
        "title": "Joint AEP and Packing Lemma Independent-Pair Bound",
        "category": "ch3-4-aep",
        "authors": "Claude E. Shannon; Thomas M. Cover; Abbas El Gamal and Young-Han Kim",
        "year": "1975",
        "reference": "Cover & Thomas, Theorem 7.6.1; El Gamal & Kim, §2.5 & Lemma 3.1",
        "tags": ["joint-aep", "packing-lemma", "typicality", "ch7"],
        "statement": (
            "For the jointly weakly typical set $A_\\varepsilon^{(n)}(X, Y)$ of an i.i.d. pair $(X^n, Y^n) \\sim P_{XY}^n$:\n"
            "1. $P_{XY}^n(A_\\varepsilon^{(n)}) \\to 1$ with explicit Chebyshev–union rate $O(1/(n\\varepsilon^2))$.\n"
            "2. $(1 - \\delta) 2^{n(H(X,Y)-\\varepsilon)} \\le |A_\\varepsilon^{(n)}| \\le 2^{n(H(X,Y)+\\varepsilon)}$ eventually.\n"
            "3. For an independent pair $(\\tilde X^n, \\tilde Y^n) \\sim P_X^n \\times P_Y^n$,\n"
            "$$(1 - \\delta) 2^{-n(I(X; Y) + 3\\varepsilon)} \\le (P_X^n \\times P_Y^n)(A_\\varepsilon^{(n)}) \\le 2^{-n(I(X; Y) - 3\\varepsilon)}.$$"
        ),
        "proof_notes": (
            "Built directly on `weakTypicalSet` via a union bound on the three marginals "
            "$P_X, P_Y, P_{XY}$ and exact product-probability bounds on $A_\\varepsilon^{(n)}$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "jointIidDist_prob_not_typical_le"),
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "joint_aep_prob_tendsto_one"),
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "jointTypicalSet_card_le"),
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "jointTypicalSet_indep_prob_le"),
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "jointTypicalSet_indep_prob_ge"),
        ],
        "related_open": [
            "broadcast-channel",
            "relay-channel",
            "dm-interference-channel-capacity",
            "cognitive-interference-channel",
        ],
    },
    {
        "id": "fekete-and-entropy-rate",
        "title": "Fekete's Subadditivity Lemma and Existence of Stationary Entropy Rate",
        "category": "ch3-4-aep",
        "authors": "Michael Fekete; Claude E. Shannon",
        "year": "1923",
        "reference": "Cover & Thomas, Theorem 4.2.1; bridged to Mathlib.Analysis.Subadditive",
        "tags": ["fekete", "subadditivity", "entropy-rate", "ch4"],
        "statement": (
            "For any subadditive sequence $a(m + n) \\le a(m) + a(n)$ with linear lower bound "
            "$a(n) \\ge c n$, $\\lim_{n \\to \\infty} a(n)/n = \\inf_{k \\ge 1} a(k)/k$ "
            "(and dually for superadditive sequences). In particular, for any stationary process "
            "$(X_1, X_2, \\dots)$, the entropy rate $\\lim_{n \\to \\infty} H(X_1, \\dots, X_n)/n$ "
            "exists and equals $\\inf_{k \\ge 1} H(X_1, \\dots, X_k)/k$."
        ),
        "proof_notes": (
            "Bridges directly to Mathlib's `Subadditive.tendsto_lim` (`Mathlib.Analysis.Subadditive`), "
            "derives the dual superadditive theorem, and proves `shannonEntropy (P (m + n)) ≤ "
            "shannonEntropy (P m) + shannonEntropy (P n)` for shift-invariant block distributions."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "fekete_subadditive_tendsto"),
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "fekete_superadditive_tendsto"),
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "stationary_entropy_subadd"),
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "stationary_entropyRate_exists"),
        ],
        "related_open": [
            "deletion-channel",
            "insertion-deletion-channel",
            "binary-duplication-channel",
            "finite-state-channel-capacity",
            "shannon-capacity-c7",
        ],
    },

    # ------------------------------------------------------------------ Ch. 5
    {
        "id": "kraft-mcmillan-theorem",
        "title": "Kraft–McMillan Inequality and Kraft Prefix-Free Code Existence",
        "category": "ch5-compression",
        "authors": "Leon G. Kraft; Brockway McMillan",
        "year": "1949",
        "reference": "Cover & Thomas, Theorems 5.2.1 & 5.5.1; Mathlib.InformationTheory.Coding.KraftMcMillan",
        "tags": ["kraft-mcmillan", "prefix-free", "uniquely-decodable", "ch5"],
        "statement": (
            "For any uniquely decodable code $S$ over a $D$-ary alphabet ($D = |\\beta| \\ge 1$),\n"
            "$$\\sum_{w \\in S} D^{-|w|} \\le 1.$$\n"
            "Conversely, for any finite family of codeword lengths $\\ell_1, \\dots, \\ell_m \\in \\mathbb{N}$ "
            "satisfying $\\sum_i D^{-\\ell_i} \\le 1$, there exists an injective prefix-free $D$-ary code "
            "with $|c(i)| = \\ell_i$."
        ),
        "proof_notes": (
            "The necessity half re-exports Mathlib's `IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`. "
            "The converse (`exists_prefixFree_code_of_kraft`) is proved constructively by sorting lengths "
            "via `Tuple.sort` and assigning base-$D$ cumulative-sum codewords."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/Mathlib.lean", "kraft_mcmillan_inequality"),
            ("lean/InfoTheory/Bridge/Coding.lean", "exists_prefixFree_code_of_kraft"),
        ],
        "related_open": [
            "universal-lossy-redundancy",
            "zero-error-source-coding-side-info",
            "interactive-info-complexity-compression",
        ],
    },
    {
        "id": "shannon-source-coding",
        "title": "Shannon's Variable-Length Source Coding Theorem (Converse & Shannon–Fano)",
        "category": "ch5-compression",
        "authors": "Claude E. Shannon; Robert M. Fano",
        "year": "1948",
        "reference": "Cover & Thomas, Theorems 5.3.1 & 5.4.1",
        "tags": ["source-coding", "shannon-fano", "compression", "ch5"],
        "statement": (
            "For any finite distribution $P$ and $D$-ary alphabet ($D \\ge 2$):\n"
            "- **Converse:** Every injective uniquely decodable code $c$ satisfies "
            "$\\mathbb{E}[|c(X)|] \\ge H(P) / \\log_2 D$.\n"
            "- **Achievability:** There exists an injective prefix-free code $c$ with "
            "$\\mathbb{E}[|c(X)|] < H(P) / \\log_2 D + 1$ (on positive support, and $\\le H(P)/\\log_2 D + 1$ "
            "on all of $\\mathcal{X}$ even with zero-mass atoms)."
        ),
        "proof_notes": (
            "The converse pairs Kraft–McMillan with Gibbs' inequality (`klDivergence_nonneg`). "
            "Achievability sets $\\ell(x) = \\lceil -\\log_D P(x) \\rceil$ and invokes "
            "`exists_prefixFree_code_of_kraft`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/Coding.lean", "source_coding_converse"),
            ("lean/InfoTheory/Bridge/Coding.lean", "source_coding_converse_prefixFree"),
            ("lean/InfoTheory/Bridge/Coding.lean", "shannon_fano_achievability"),
            ("lean/InfoTheory/Bridge/Coding.lean", "shannon_fano_achievability_support"),
            ("lean/InfoTheory/Bridge/Coding.lean", "shannon_fano_achievability_le"),
        ],
        "related_open": [
            "universal-lossy-redundancy",
            "interactive-info-complexity-compression",
            "zero-error-source-coding-side-info",
        ],
    },

    # ------------------------------------------------------------------ Ch. 7
    {
        "id": "shannon-channel-coding",
        "title": "Shannon's Channel Coding Theorem (Achievability and Weak Converse)",
        "category": "ch7-channel",
        "authors": "Claude E. Shannon",
        "year": "1948",
        "reference": "Cover & Thomas, Theorem 7.7.1 & §7.9",
        "tags": ["shannon-capacity", "channel-coding", "random-coding", "flagship", "ch7"],
        "statement": (
            "For every discrete memoryless channel $W : \\mathcal{X} \\to \\mathcal{Y}$, the "
            "operational capacity (supremum of rates achievable with vanishing average block error "
            "probability) equals the single-letter information capacity:\n"
            "$$C_{\\mathrm{op}}(W) = C(W) = \\sup_{P_X} I(X; Y).$$"
        ),
        "proof_notes": (
            "Both halves proved end-to-end against `InfoTheory.Core.Channels` (`DMC`, `DMC.power`, "
            "`DMC.capacity`, `dmcAvgError`). Achievability averages error over i.i.d. random codebooks "
            "`codebookProb` with unique joint-typicality decoding (`jointTypicalDec`), invoking "
            "`joint_aep_prob_tendsto_one` and `jointTypicalSet_indep_prob_le`. The converse combines "
            "multi-letter mutual-information subadditivity (`dmcPower_mutualInfo_le_mul_capacity`) "
            "with Fano's inequality (`dmcAvgError_rate_converse`)."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "dmcPower_mutualInfo_le_sum"),
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "dmcPower_mutualInfo_le_mul_capacity"),
            ("lean/InfoTheory/Bridge/ChannelCoding.lean", "dmcAvgError_rate_converse"),
            ("lean/InfoTheory/Bridge/ChannelAchievability.lean", "dmc_random_coding_bound"),
            ("lean/InfoTheory/Bridge/ChannelAchievability.lean", "shannon_channel_coding_achievability"),
            ("lean/InfoTheory/Bridge/ChannelAchievability.lean", "shannon_channel_coding_converse"),
            ("lean/InfoTheory/Bridge/ChannelAchievability.lean", "shannon_channel_coding_theorem"),
        ],
        "related_open": [
            "deletion-channel",
            "insertion-deletion-channel",
            "finite-state-channel-capacity",
            "bsc-reliability-function",
            "dmc-zero-rate-error-exponent",
            "reed-muller-capacity-general-dmc",
            "polar-code-scaling-exponent",
            "dna-storage-unordered-channel",
        ],
        "analogous_open": [
            "classical-capacity-additivity-threshold",
        ],
    },
    {
        "id": "bsc-and-bec-capacity",
        "title": "Exact Capacities of the Binary Symmetric, Erasure, and Noiseless Channels",
        "category": "ch7-channel",
        "authors": "Claude E. Shannon; Peter Elias",
        "year": "1955",
        "reference": "Cover & Thomas, §§7.1.4–7.1.5",
        "tags": ["bsc", "bec", "capacity", "ch7"],
        "statement": (
            "For $p, \\varepsilon \\in [0, 1]$ and any nonempty finite alphabet $\\mathcal{X}$:\n"
            "$$C(\\mathrm{BSC}(p)) = 1 - h(p), \\qquad C(\\mathrm{BEC}(\\varepsilon)) = 1 - \\varepsilon, "
            "\\qquad C(\\mathrm{Id}_{\\mathcal{X}}) = \\log_2 |\\mathcal{X}|.$$"
        ),
        "proof_notes": (
            "Proved directly against `InfoTheory.Core.Channels.{bsc, bec}` in `Known/Channels.lean`, "
            "serving as both a textbook lemma base and a machine-checked sanity certification of the "
            "Core DMC definitions."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/Channels.lean", "bsc_capacity"),
            ("lean/InfoTheory/Known/Channels.lean", "bec_capacity"),
            ("lean/InfoTheory/Known/Channels.lean", "noiselessChannel_capacity"),
        ],
        "related_open": [
            "bsc-reliability-function",
            "primitive-relay-channel-bsc",
            "binary-symmetric-z-interference-channel",
            "binary-skew-symmetric-bc",
            "noisy-interactive-communication-rate",
        ],
    },
    {
        "id": "deletion-channel-bounds",
        "title": "Binary Deletion Channel Baseline Capacity Bounds",
        "category": "ch7-channel",
        "authors": "Roland L. Dobrushin; Michael Mitzenmacher",
        "year": "1967",
        "reference": "Mitzenmacher (2009) Survey; Dobrushin (1967)",
        "tags": ["deletion-channel", "synchronization", "bounds", "ch7"],
        "statement": (
            "For the i.i.d. binary deletion channel with deletion probability $d \\in [0, 1]$:\n"
            "$$C_{\\mathrm{del}}(0) = 1, \\qquad 0 \\le C_{\\mathrm{del}}(d) \\le \\frac{1}{n} \\max_{P_{X^n}} I(X^n; Y) \\quad (\\forall n \\ge 1), \\qquad C_{\\mathrm{del}}(d) \\le 1 - d.$$"
        ),
        "proof_notes": (
            "Proved directly against `InfoTheory.Core.Channels.binaryDeletionCapacity` in "
            "`Known/Channels.lean` (and certified for all three deletion-channel open statements "
            "under `Known/Certificates/`)."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/Channels.lean", "binaryDeletionCapacity_zero"),
            ("lean/InfoTheory/Known/Channels.lean", "binaryDeletionCapacity_le_one_sub"),
            ("lean/InfoTheory/Known/Channels.lean", "binaryDeletionCapacity_le_maxMI_div"),
            ("lean/InfoTheory/Known/Channels.lean", "binaryDeletionMaxMI_one"),
        ],
        "related_open": [
            "deletion-channel",
            "deletion-channel-small-d-asymptotics",
            "deletion-channel-high-d-limit",
            "insertion-deletion-channel",
            "trace-reconstruction-worst-case",
            "trace-reconstruction-average-case",
        ],
    },
    {
        "id": "gallager-random-coding-exponent",
        "title": "Gallager's Random-Coding Error Exponent Bound",
        "category": "ch7-channel",
        "authors": "Robert G. Gallager",
        "year": "1965",
        "reference": "Gallager (1965), Theorem 1; Cover & Thomas, Ch. 7",
        "tags": ["error-exponent", "gallager", "reliability-function", "ch7"],
        "statement": (
            "For any DMC $W$, input distribution $P$, blocklength $n$, message size $M \\ge 1$, "
            "and $\\rho \\in [0, 1]$, there exists an $(n, M)$ block code with\n"
            "$$P_e \\le (M - 1)^\\rho \\, 2^{-n E_0(\\rho, P, W)}, \\qquad "
            "E_0(\\rho, P, W) = -\\log_2 \\sum_y \\left(\\sum_x P(x) W(y|x)^{\\frac{1}{1+\\rho}}\\right)^{1+\\rho}.$$\n"
            "Consequently, for every positive DMC $W$ and rate $R > 0$, the random-coding exponent "
            "lower-bounds the reliability function: $E_r(R, W) \\le E(R, W)$."
        ),
        "proof_notes": (
            "Implements Gallager's 1965 ML-decoding proof over finite random-codebook ensembles "
            "using concavity of $t \\mapsto t^\\rho$ on $[0, \\infty)$, and bridges directly to "
            "`InfoTheory.Core.Channels.{randomCodingExponent, reliabilityFunction}`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "gallager_random_coding_bound"),
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "dmcMinError_le_gallager"),
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "gallager_le_reliabilityFunction"),
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "randomCodingExponent_le_reliabilityFunction"),
        ],
        "related_open": [
            "bsc-reliability-function",
            "dmc-zero-rate-error-exponent",
            "awgn-feedback-error-exponent",
        ],
    },
    {
        "id": "feedback-does-not-increase-dmc-capacity",
        "title": "Feedback Does Not Increase the Capacity of a Discrete Memoryless Channel",
        "category": "ch7-channel",
        "authors": "Claude E. Shannon",
        "year": "1956",
        "reference": "Cover & Thomas, Theorem 7.12.1; El Gamal & Kim, §3.1.2",
        "tags": ["feedback", "dmc", "capacity", "converse", "ch7"],
        "statement": (
            "For every discrete memoryless channel $W : \\mathcal{X} \\to \\mathcal{Y}$ with noiseless "
            "causal output feedback (where the $i$-th transmitted symbol $X_i(M, Y^{i-1})$ may depend "
            "adaptively on all past outputs), every $(n, M)$ feedback code satisfies "
            "$I(M; Y^n) \\le n C(W)$, and the operational feedback capacity equals the non-feedback capacity:\n"
            "$$C_{\\mathrm{FB}}(W) = C(W).$$\n"
            "As a multi-user corollary, over any DM-MAC with feedback whose output ignores user 2 "
            "($W(y \\mid x_1, x_2) = V(y \\mid x_1)$), every achievable pair satisfies $R_1 \\le C(V)$."
        ),
        "proof_notes": (
            "Proves causal product normalization (`feedbackCausalProd_sum_one`), inducts on blocklength "
            "$n$ peeling off the last channel use to prove `dmcFeedback_mutualInfo_le_mul_capacity`, "
            "combines with sharp Fano's inequality (`dmcFeedback_weak_converse`), wraps "
            "`shannon_channel_coding_achievability` for the achievability direction, and extracts "
            "the silent-user MAC-with-feedback converse `isMACFeedbackAchievable_le_capacity_of_ignores_second`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/FeedbackConverse.lean", "dmcFeedback_mutualInfo_le_mul_capacity"),
            ("lean/InfoTheory/Bridge/FeedbackConverse.lean", "dmcFeedback_weak_converse"),
            ("lean/InfoTheory/Bridge/FeedbackConverse.lean", "dmc_feedback_converse"),
            ("lean/InfoTheory/Bridge/FeedbackConverse.lean", "dmc_feedback_capacity_theorem"),
            ("lean/InfoTheory/Bridge/FeedbackConverse.lean", "macFeedbackCapacityRegion_fst_le_of_ignores_second"),
        ],
        "related_open": [
            "mac-with-feedback",
            "wiretap-with-feedback-capacity",
            "zero-error-feedback-variable-length",
        ],
        "analogous_open": [
            "timing-channel-general-queue",
            "gaussian-bc-feedback-sum-capacity",
            "gaussian-mac-feedback-linear-optimality",
        ],
    },
    {
        "id": "cost-constrained-dmc-coding",
        "title": "Cost-Constrained Channel Coding Achievability (Random Coding & Expurgation)",
        "category": "ch7-channel",
        "authors": "Robert G. Gallager; Abbas El Gamal and Young-Han Kim",
        "year": "1968",
        "reference": "El Gamal & Kim, §3.3; Gallager, §7.3; Cover & Thomas, §9.1",
        "tags": ["cost-constraint", "power-constraint", "expurgation", "channel-coding", "ch7"],
        "statement": (
            "For any discrete memoryless channel $W : \\mathcal{X} \\to \\mathcal{Y}$, input distribution "
            "$P_X$, single-letter input cost $b : \\mathcal{X} \\to \\mathbb{R}$, and cost budget $B$ "
            "satisfying $\\mathbb{E}_{P_X}[b(X)] < B$, every rate $0 \\le R < I(P_X, W)$ is achievable "
            "by $(n, \\max(1, \\lfloor 2^{nR} \\rfloor))$ block codes in which **every** codeword obeys "
            "the deterministic per-codeword cost constraint $\\sum_{i=1}^n b(x_i(m)) \\le n B$ and the "
            "average error probability is at most $\\delta$ for all sufficiently large $n$."
        ),
        "proof_notes": (
            "Combines an i.i.d. Chebyshev bound on empirical cost violation "
            "(`violProb_le`, `violProb_eventually_le`), random-codebook averaging of error plus violation fraction "
            "(`exists_codebook_err_add_viol_le`), and deterministic expurgation of half the codebook "
            "(`exists_subcode_of_err_add_viol_le`) on top of `Bridge/ChannelAchievability.lean` — "
            "serving as the finite-alphabet engine behind the operational AWGN capacity achievability proof."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/CostConstrainedCoding.lean", "violProb_le"),
            ("lean/InfoTheory/Known/CostConstrainedCoding.lean", "exists_codebook_err_add_viol_le"),
            ("lean/InfoTheory/Known/CostConstrainedCoding.lean", "exists_subcode_of_err_add_viol_le"),
            ("lean/InfoTheory/Known/CostConstrainedCoding.lean", "dmc_cost_constrained_achievable"),
        ],
        "related_open": [
            "amplitude-constrained-awgn-support",
            "poisson-channel-discrete-capacity",
        ],
        "analogous_open": [
            "gaussian-interference-channel",
            "gaussian-relay-channel-capacity",
        ],
    },

    # ------------------------------------------------------------------ Ch. 8–9
    {
        "id": "gaussian-max-entropy",
        "title": "Gaussian Differential Entropy, Scaling, and Maximum Entropy Theorem",
        "category": "ch8-9-gaussian",
        "authors": "Claude E. Shannon",
        "year": "1948",
        "reference": "Cover & Thomas, Theorems 8.4.1, 8.6.3, 8.6.4 & 8.6.5",
        "tags": ["differential-entropy", "gaussian", "max-entropy", "entropy-power", "ch8"],
        "statement": (
            "For a centered Gaussian $\\mathcal{N}(0, v)$ ($v > 0$), its differential entropy and "
            "entropy power are\n"
            "$$h(\\mathcal{N}(0, v)) = \\frac{1}{2}\\ln(2\\pi e v), \\qquad N(\\mathcal{N}(0, v)) = v,$$\n"
            "and for any 1D density $f$ with finite differential entropy and second moment $\\mathbb{E}[X^2] \\le v$,\n"
            "$$h(f) \\le \\frac{1}{2}\\ln(2\\pi e v).$$\n"
            "Moreover, $h(aX + b) = h(X) + \\ln|a|$, and for product Gaussians in $\\mathbb{R}^d$, "
            "$h(\\mathcal{N}(0, \\mathrm{diag}(v))) = \\frac{1}{2}\\sum_{i=1}^d \\ln(2\\pi e v_i)$."
        ),
        "proof_notes": (
            "Bridges `InfoTheory.Core.Entropy.gaussianPdf1D` to Mathlib's `ProbabilityTheory.gaussianPDFReal` "
            "and `variance_fun_id_gaussianReal`, and proves maximum entropy pointwise from Mathlib's "
            "`InformationTheory.klFun_nonneg`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/Gaussian.lean", "diffEntropy_gaussianDensity1D"),
            ("lean/InfoTheory/Bridge/Gaussian.lean", "entropyPower_gaussianDensity1D"),
            ("lean/InfoTheory/Bridge/Gaussian.lean", "diffEntropy_le_gaussian"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "diffEntropy_translateDensity1D"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "diffEntropy_scaleDensity1D"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "diffEntropy_gaussianProductDensity"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "entropyPower_isotropicGaussian"),
        ],
        "related_open": [
            "conditional-entropy-power-conjecture",
            "renyi-entropy-power-sharp",
            "discrete-entropy-power-inequality",
            "gaussian-optimality-mutual-information",
            "mmse-dimension-single-crossing",
        ],
        "analogous_open": [
            "quantum-entropy-power-sharp",
            "timing-channel-general-queue",
        ],
    },
    {
        "id": "awgn-capacity-bound",
        "title": "AWGN Channel Capacity Upper Bound and Gaussian Optimality",
        "category": "ch8-9-gaussian",
        "authors": "Claude E. Shannon",
        "year": "1948",
        "reference": "Cover & Thomas, Theorem 9.1.1 & §9.2",
        "tags": ["awgn", "gaussian-channel", "capacity", "ch9"],
        "statement": (
            "For an additive white Gaussian noise channel $Y = X + Z$ with $Z \\sim \\mathcal{N}(0, N)$ ($N > 0$) "
            "independent of a density $X$ with finite second moment $\\mathbb{E}[X^2] \\le P$ and finite output "
            "differential entropy,\n"
            "$$h(X + Z) - h(Z) \\le \\frac{1}{2}\\ln\\left(1 + \\frac{P}{N}\\right),$$\n"
            "with exact equality for $X \\sim \\mathcal{N}(0, P)$ ($P > 0$, where $X + Z \\sim \\mathcal{N}(0, P + N)$). "
            "Across $n$ uses with average power $\\frac{1}{n}\\sum_i P_i \\le P$, Jensen concavity gives "
            "$\\frac{1}{n}\\sum_i \\frac{1}{2}\\ln(1 + P_i/N) \\le \\frac{1}{2}\\ln(1 + P/N)$."
        ),
        "proof_notes": (
            "Constructs `awgnOutputDensity` via Fubini/Tonelli convolution with `gaussianDensity1D`, "
            "proves $\\mathbb{E}[(X+Z)^2] = \\mathbb{E}[X^2] + N$ without requiring zero mean, and "
            "applies `diffEntropy_le_gaussian` together with exact Gaussian convolution."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "awgnOutputDensity_secondMoment"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "awgn_mutualInfo_le_capacity"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "awgnOutputDensity_gaussian"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "awgn_mutualInfo_gaussian"),
            ("lean/InfoTheory/Bridge/ContinuousIT.lean", "awgn_multiletter_power_jensen"),
        ],
        "related_open": [
            "gaussian-interference-channel",
            "gaussian-relay-channel-capacity",
            "gaussian-multiple-descriptions-3",
            "awgn-feedback-error-exponent",
        ],
    },
    {
        "id": "awgn-operational-converse",
        "title": "Shannon's AWGN Channel Coding Theorem (Operational Capacity = ½ log₂(1 + P/N))",
        "category": "ch8-9-gaussian",
        "authors": "Claude E. Shannon",
        "year": "1948",
        "reference": "Cover & Thomas, Theorem 9.1.1; El Gamal & Kim, Theorem 3.2 & §3.3",
        "tags": ["awgn", "operational-capacity", "measurable-codes", "flagship", "ch9"],
        "statement": (
            "Over the memoryless AWGN channel $Y_i = X_i + Z_i$ ($Z_i \\sim \\mathcal{N}(0, N)$ i.i.d., "
            "$P \\ge 0$, $N > 0$) with measurable decoders, per-codeword power constraint "
            "$\\sum_{i=1}^n x_i(m)^2 \\le n P$, and `ENNReal`-valued average error probabilities:\n"
            "$$C_{\\mathrm{op}}^{\\mathrm{AWGN}}(P, N) = \\frac{1}{2}\\log_2\\left(1 + \\frac{P}{N}\\right).$$\n"
            "Every rate $0 \\le R < \\frac{1}{2}\\log_2(1 + P/N)$ is operationally achievable, and no rate "
            "$R > \\frac{1}{2}\\log_2(1 + P/N)$ is achievable (note: average-message error here matches "
            "the maximal-error capacity of Cover & Thomas Thm. 9.1.1)."
        ),
        "proof_notes": (
            "Proved end-to-end against `Core/GaussianOperational.lean`: `Known/GaussianChannel.lean` "
            "excludes non-measurable decoders, proves the operational converse via exact Gaussian "
            "likelihood-ratio change of measure against $\\mathcal{N}(0, (P+N)I_n)$, and proves the "
            "BPSK lower bound; `Known/GaussianAchievability.lean` proves full achievability "
            "(`isAwgnAchievable_of_lt_capacity`) by fine quantization of truncated Gaussian inputs and "
            "outputs into finite DMCs and invoking `Bridge.shannon_channel_coding_achievability`, "
            "yielding exact operational equality `awgnOperationalCapacity_eq`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/GaussianChannel.lean", "awgn_code_converse"),
            ("lean/InfoTheory/Known/GaussianChannel.lean", "awgnOperationalCapacity_le"),
            ("lean/InfoTheory/Known/GaussianAchievability.lean", "isAwgnAchievable_of_lt_capacity"),
            ("lean/InfoTheory/Known/GaussianAchievability.lean", "awgnOperationalCapacity_eq"),
            ("lean/InfoTheory/Known/GaussianAchievability.lean", "isAwgnAchievable_iff_of_ne"),
        ],
        "related_open": [
            "amplitude-constrained-awgn-support",
            "gaussian-interference-channel",
            "gaussian-relay-channel-capacity",
            "gaussian-bc-feedback-sum-capacity",
            "gaussian-mac-feedback-linear-optimality",
            "awgn-feedback-error-exponent",
        ],
    },

    # ------------------------------------------------------------------ Ch. 10
    {
        "id": "rate-distortion-and-covering",
        "title": "Covering Lemma and Shannon's Rate–Distortion Theorem (Converse & Achievability)",
        "category": "ch10-rate-distortion",
        "authors": "Claude E. Shannon; Toby Berger",
        "year": "1959",
        "reference": "Cover & Thomas, Theorem 10.2.1 & Lemma 10.6.1; El Gamal & Kim, Lemma 3.3",
        "tags": ["rate-distortion", "covering-lemma", "lossy-coding", "ch10"],
        "statement": (
            "For a finite i.i.d. source $P$ and bounded single-letter distortion $d : \\mathcal{X} \\times \\hat{\\mathcal{X}} \\to \\mathbb{R}_{\\ge 0}$:\n"
            "- For all feasible distortions $D \\ge D_{\\min}$, $R(D)$ is nonnegative, nonincreasing, convex, and right-continuous in $D$.\n"
            "- **Converse:** Every $(n, M)$ block code with expected per-symbol distortion $\\le D$ obeys "
            "$\\frac{1}{n}\\log_2 M \\ge R(D)$.\n"
            "- **Covering Lemma:** $M$ i.i.d. codewords $\\sim P_{\\hat X}^n$ cover $X^n \\sim P_X^n$ in "
            "$A_\\varepsilon^{(n)}$ with probability $\\to 1$ whenever $R > I(X; \\hat X) + 3\\varepsilon$.\n"
            "- **Operational Equality:** For every feasible $D \\ge D_{\\min}$, the operational rate–distortion "
            "function equals the single-letter information rate–distortion function: $R_{\\mathrm{op}}(D) = R(D)$."
        ),
        "proof_notes": (
            "Proves convexity of $I(X; \\hat X)$ in the test channel calculus-free via strong subadditivity, "
            "establishes right-continuity of $R(D)$ at every feasible $D$ (including $D = D_{\\min}$) via "
            "compactness of the feasible joint-distribution simplex, derives the converse via time-sharing mixtures, "
            "proves Cover & Thomas Lemma 10.5.3 $(1 - xy)^M \\le 1 - x + e^{-My}$ for the Covering Lemma, and "
            "combines both halves into the full operational equality `shannon_rate_distortion_theorem` against "
            "`InfoTheory.Core.SourceCoding.rateDistortion`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/RateDistortion.lean", "rateDistortion_convex"),
            ("lean/InfoTheory/Bridge/RateDistortion.lean", "rateDistortion_rightContinuous"),
            ("lean/InfoTheory/Bridge/RateDistortion.lean", "rateDistortion_converse"),
            ("lean/InfoTheory/Bridge/RateDistortion.lean", "covering_lemma"),
            ("lean/InfoTheory/Bridge/RateDistortion.lean", "covering_lemma_tendsto_zero"),
            ("lean/InfoTheory/Bridge/RateDistortion.lean", "rateDistortion_achievability"),
            ("lean/InfoTheory/Bridge/RateDistortion.lean", "shannon_rate_distortion_theorem"),
        ],
        "related_open": [
            "multiterminal-source-coding",
            "multiple-descriptions-general",
            "gaussian-multiple-descriptions-3",
            "ceo-problem-general",
            "gray-wyner-lossy",
            "cascade-rate-distortion-side-info",
            "non-asymptotic-lossy-dispersion",
            "universal-lossy-redundancy",
        ],
    },
    {
        "id": "markov-source-shannon-lower-bound",
        "title": "Binary Symmetric Markov Source Entropy Rate & Shannon Lower Bound",
        "category": "ch10-rate-distortion",
        "authors": "Robert M. Gray; Toby Berger",
        "year": "1970",
        "reference": "Gray (1970/1971); Berger (1971), §4.3",
        "tags": ["markov-source", "shannon-lower-bound", "rate-distortion", "ch10"],
        "statement": (
            "For the stationary binary symmetric Markov source $\\mathrm{BSMS}(q)$ with switching "
            "probability $q \\in [0, 1]$ under block-averaged Hamming distortion:\n"
            "- Its $(n+1)$-block entropy is $H(X^{n+1}) = 1 + n\\,h(q)$.\n"
            "- Its rate–distortion function $R(D) = \\inf_{n \\ge 1} R_n(D)/n$ satisfies $0 \\le R(D) \\le 1$ "
            "(for $D \\ge 0$), $R(D) = 0$ for $D \\ge 1/2$, and the **Shannon lower bound**\n"
            "$$R(D) \\ge h(q) - h(D) \\qquad (0 \\le D \\le 1/2).$$\n"
            "- For $0 < q < 1/2$, Gray's critical distortion $D_c(q) = \\frac{1}{2}(1 - \\sqrt{1 - (q/(1-q))^2})$ "
            "satisfies $0 < D_c(q) < 1/2$ (classically, Gray 1970 showed the lower bound is tight on $[0, D_c(q)]$; "
            "tightness itself is not yet formalized here)."
        ),
        "proof_notes": (
            "Proved in `Known/MarkovSource.lean` via the reversible prepend construction `bsmsBlock`, "
            "exact block entropy induction, and a block-level Hamming-error Fano/entropy lower bound "
            "combined with concavity of binary entropy."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/MarkovSource.lean", "entropy_bsmsBlock"),
            ("lean/InfoTheory/Known/MarkovSource.lean", "rateDistortion_eq_zero_of_half_le"),
            ("lean/InfoTheory/Known/MarkovSource.lean", "shannon_lower_bound"),
            ("lean/InfoTheory/Known/MarkovSource.lean", "criticalDistortion_pos"),
            ("lean/InfoTheory/Known/MarkovSource.lean", "criticalDistortion_lt_half"),
        ],
        "related_open": [],
        "analogous_open": [
            "universal-lossy-redundancy",
        ],
    },

    # ------------------------------------------------------------------ Ch. 11
    {
        "id": "pinsker-inequality",
        "title": "Pinsker's Inequality Relating Total Variation and KL Divergence",
        "category": "ch11-types",
        "authors": "Mark S. Pinsker; Imre Csiszár; Solomon Kullback; J. H. B. Kemperman",
        "year": "1964",
        "reference": "Cover & Thomas, Lemma 11.6.1",
        "tags": ["pinsker", "total-variation", "kl-divergence", "ch11"],
        "statement": (
            "For any two distributions $P, Q$ on a finite alphabet $\\mathcal{X}$ with $P \\ll Q$,\n"
            "$$2 \\, \\mathrm{TV}(P, Q)^2 \\le (\\ln 2) \\, D(P \\| Q),$$\n"
            "where $\\mathrm{TV}(P, Q) = \\frac{1}{2} \\sum_{x \\in \\mathcal{X}} |P(x) - Q(x)|$ and $D(P \\| Q)$ is in bits."
        ),
        "proof_notes": (
            "Proves the binary case on `Bool` via the mean-value theorem on $f(t) = D(\\mathrm{Bern}(p) \\| "
            "\\mathrm{Bern}(t)) \\ln 2 - 2(p - t)^2$, then lifts to arbitrary finite alphabets in one step "
            "via Scheffé's identity and deterministic-map DPI (`klDivergence_map_le`)."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/Coding.lean", "pinsker_bool"),
            ("lean/InfoTheory/Bridge/Coding.lean", "tvDistance_eq_scheffe_diff"),
            ("lean/InfoTheory/Bridge/Coding.lean", "pinsker_inequality"),
        ],
        "related_open": [
            "minimax-kl-large-alphabet",
            "ldp-minimax-kl-sharp",
            "covert-communication-second-order",
            "sdpi-kl-vs-chisq-equality",
        ],
    },
    {
        "id": "method-of-types-and-sanov",
        "title": "Method of Types and Sanov's Large-Deviations Theorem",
        "category": "ch11-types",
        "authors": "Imre Csiszár; Ivan N. Sanov",
        "year": "1957",
        "reference": "Cover & Thomas, Theorems 11.1.1–11.1.4 & 11.4.1",
        "tags": ["method-of-types", "sanov", "large-deviations", "ch11"],
        "statement": (
            "For sequences of length $n \\ge 1$ over a finite alphabet $\\mathcal{X}$:\n"
            "1. The number of empirical types satisfies $|\\mathcal{P}_n(\\mathcal{X})| \\le (n + 1)^{|\\mathcal{X}|}$.\n"
            "2. Every $x^n$ of type $P$ with $P \\ll Q$ has exact probability $Q^n(x^n) = 2^{-n(H(P) + D(P \\| Q))}$.\n"
            "3. Each type class $T(P)$ satisfies $(n+1)^{-|\\mathcal{X}|} 2^{n H(P)} \\le |T(P)| \\le 2^{n H(P)}$, "
            "and whenever $P \\ll Q$, $(n+1)^{-|\\mathcal{X}|} 2^{-n D(P \\| Q)} \\le Q^n(T(P)) \\le 2^{-n D(P \\| Q)}$.\n"
            "4. **Sanov's Theorem (Upper, Lower, and Asymptotic Limit):** For any set $E$ of distributions such "
            "that $D(P \\| Q) \\ge d$ whenever $P \\in E$ and $P \\ll Q$, "
            "$Q^n(\\{x^n : \\hat P_{x^n} \\in E\\}) \\le (n+1)^{|\\mathcal{X}|} 2^{-n d}$; "
            "for any $\\ell_\\infty$-interior point $P \\in E$ with $P \\ll Q$, eventually "
            "$Q^n(\\{x^n : \\hat P_{x^n} \\in E\\}) \\ge 2^{-n(D(P \\| Q) + \\delta)}$; and when $d$ is approached "
            "by $\\ell_\\infty$-interior points $P \\in E$ with $P \\ll Q$, "
            "$-\\frac{1}{n}\\log_2 Q^n(\\{x^n : \\hat P_{x^n} \\in E\\}) \\to d$ (valid for arbitrary $Q$, "
            "including distributions with zero-mass atoms)."
        ),
        "proof_notes": (
            "The lower bound on $|T(P)|$ uses exact multinomial counting $|T(P)| \\prod_a N(a|x)! = n!$ "
            "to show $P^n(T(P)) = \\max_{P'} P^n(T(P')) \\ge (n+1)^{-|\\mathcal{X}|}$. Sanov's lower bound "
            "and limit constructively approximate any interior $P \\in E$ by empirical types $P_n \\ll P$ "
            "(`exists_empiricalType_approx`) and combine `typeClass_prob_ge` with continuity of $D(\\cdot \\| Q)$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "card_typesSet_le"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "iidDist_pmf_eq_type"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "typeClass_card_le"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "typeClass_card_ge"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "typeClass_prob_le"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "typeClass_prob_ge"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "sanov_upper_bound"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "sanov_lower_bound_interior"),
            ("lean/InfoTheory/Bridge/MethodOfTypes.lean", "sanov_theorem_tendsto"),
        ],
        "related_open": [
            "distributed-hypothesis-testing-exponent",
            "universal-lossy-redundancy",
            "bsc-reliability-function",
            "dmc-zero-rate-error-exponent",
        ],
    },
    {
        "id": "chernoff-stein-lemma",
        "title": "Chernoff–Stein Lemma for Binary Hypothesis Testing",
        "category": "ch11-types",
        "authors": "Herman Chernoff; Charles Stein",
        "year": "1952",
        "reference": "Cover & Thomas, Theorem 11.8.3",
        "tags": ["chernoff-stein", "hypothesis-testing", "error-exponent", "ch11"],
        "statement": (
            "When testing $H_0 : P^n$ against $H_1 : Q^n$ ($P \\ll Q$) at any fixed Type-I error threshold "
            "$\\varepsilon \\in (0, 1)$, the optimal Type-II error probability $\\beta_n^*(\\varepsilon)$ satisfies\n"
            "$$\\lim_{n \\to \\infty} -\\frac{1}{n}\\log_2 \\beta_n^*(\\varepsilon) = D(P \\| Q):$$\n"
            "- **Achievability:** For every $\\delta > 0$, eventually there exist acceptance sets $A_n$ with "
            "$\\alpha_n \\le \\varepsilon$ and $\\beta_n \\le 2^{-n(D(P \\| Q) - \\delta)}$.\n"
            "- **Strong Converse:** For every $\\delta > 0$, eventually every test with $\\alpha_n \\le \\varepsilon$ "
            "satisfies $\\beta_n \\ge 2^{-n(D(P \\| Q) + \\delta)}$ (plus the finite-$n$ DPI weak converse "
            "$(1 - \\varepsilon)(-\\frac{1}{n}\\log_2 \\beta_n) \\le D(P \\| Q) + \\frac{1}{n}$)."
        ),
        "proof_notes": (
            "Achievability uses the relative-entropy typical set `relEntTypicalSet` with a finite-sum "
            "Chebyshev bound; the strong converse intersects any acceptance set $A_n$ with `relEntTypicalSet` "
            "so $P^n(A_n \\cap B_n) \\ge (1 - \\varepsilon)/2$ and transfers mass to $Q^n$ via the pointwise "
            "likelihood ratio bound; the finite-$n$ weak converse uses deterministic-map DPI (`klDivergence_map_le`)."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "klDivergence_iidDist"),
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "chernoff_stein_achievability"),
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "chernoff_stein_converse_rate"),
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "chernoff_stein_strong_converse"),
            ("lean/InfoTheory/Bridge/ErrorExponents.lean", "chernoff_stein_theorem"),
        ],
        "related_open": [
            "distributed-hypothesis-testing-exponent",
            "sbm-multi-community-threshold",
            "covert-communication-second-order",
        ],
    },

    # ------------------------------------------------------------------ Ch. 15 / EGK
    {
        "id": "slepian-wolf-theorem",
        "title": "Slepian–Wolf Distributed Lossless Source Coding Theorem",
        "category": "ch15-network",
        "authors": "David Slepian and Jack K. Wolf",
        "year": "1973",
        "reference": "Cover & Thomas, Theorem 15.4.1; El Gamal & Kim, Theorem 10.1",
        "tags": ["slepian-wolf", "distributed-compression", "random-binning", "ch15"],
        "statement": (
            "For an i.i.d. correlated source $(X^n, Y^n) \\sim P_{XY}^n$ encoded separately without "
            "communication between encoders and decoded jointly, the closed achievable rate region is\n"
            "$$\\mathcal{R}_{\\mathrm{SW}}(P_{XY}) = \\{(R_1, R_2) \\in \\mathbb{R}_{\\ge 0}^2 : "
            "R_1 \\ge H(X \\mid Y),\\; R_2 \\ge H(Y \\mid X),\\; R_1 + R_2 \\ge H(X, Y)\\}.$$"
        ),
        "proof_notes": (
            "Achievability averages over uniform random binning maps $(f_1, f_2)$ with unique joint-typicality "
            "decoding, bounding all four error events via `joint_aep_prob_tendsto_one` and conditional "
            "typical-set cardinalities. The converse applies Fano's inequality to $H(X^n \\mid Y^n)$, "
            "$H(Y^n \\mid X^n)$, and $H(X^n, Y^n)$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "slepianWolf_converse_bounds"),
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "slepian_wolf_converse"),
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "slepianWolf_random_binning_bound"),
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "slepian_wolf_achievability"),
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "slepian_wolf_theorem"),
        ],
        "related_open": [
            "multiterminal-source-coding",
            "ceo-problem-general",
            "zero-error-source-coding-side-info",
            "common-information-exact-vs-wyner",
            "gray-wyner-lossy",
            "correlated-sources-over-mac",
        ],
    },
    {
        "id": "mac-capacity-region",
        "title": "Two-User Multiple-Access Channel (MAC) Capacity Region Theorem",
        "category": "ch15-network",
        "authors": "Rudolf Ahlswede; Henry H. Liao",
        "year": "1971",
        "reference": "Cover & Thomas, Theorem 15.3.1; El Gamal & Kim, Theorem 4.3",
        "tags": ["mac", "network-it", "capacity-region", "ch15"],
        "statement": (
            "For any two-user discrete memoryless multiple-access channel $W : \\mathcal{X}_1 \\times "
            "\\mathcal{X}_2 \\to \\mathcal{Y}$, the closed operational capacity region equals the closure "
            "of the convex hull of the union over independent inputs $P_1 \\times P_2$ of the pentagons\n"
            "$$R_1 \\le I(X_1; Y \\mid X_2), \\qquad R_2 \\le I(X_2; Y \\mid X_1), \\qquad R_1 + R_2 \\le I(X_1, X_2; Y).$$"
        ),
        "proof_notes": (
            "Proved against `InfoTheory.Core.Channels.MACChannel` (using newly defined non-feedback "
            "operational achievability, since `Core` defines only the feedback MAC): random coding with "
            "3-way joint typicality achieves every pentagon (`mac_achievability_pentagon`), block "
            "concatenation yields convexity of the operational region, and Fano's inequality + "
            "multi-letter tensorization establishes the converse (`mac_converse`)."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "mac_random_coding_bound"),
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "mac_achievability_pentagon"),
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "mac_converse"),
            ("lean/InfoTheory/Bridge/NetworkIT.lean", "mac_capacity_theorem"),
        ],
        "related_open": [
            "mac-with-feedback",
            "zero-error-mac-adder",
            "correlated-sources-over-mac",
            "dm-interference-channel-capacity",
            "two-way-channel-capacity",
            "binary-multiplier-two-way-channel",
        ],
    },
    {
        "id": "mrs-gerber-and-degraded-bc",
        "title": "Mrs. Gerber's Lemma (Scalar & Vector) and Binary Degraded Broadcast Channel",
        "category": "ch15-network",
        "authors": "Aaron D. Wyner and Jacob Ziv; Patrick P. Bergmans",
        "year": "1973",
        "reference": "Wyner & Ziv (1973), Theorem 1; Cover & Thomas, §15.6.2; El Gamal & Kim, Ch. 5",
        "tags": ["mrs-gerber", "broadcast-channel", "binary-entropy", "ch15"],
        "statement": (
            "For $p \\in [0, 1/2]$, the function $u \\mapsto h(h^{-1}(u) \\star p)$ is convex on $[0, 1]$. "
            "Hence for any $X^n \\in \\{0, 1\\}^n$ passed through $\\mathrm{BSC}(p)^n$ to produce $Y^n$,\n"
            "$$\\frac{1}{n} H(Y^n \\mid U) \\ge h\\!\\left(h^{-1}\\!\\left(\\frac{1}{n} H(X^n \\mid U)\\right) \\star p\\right).$$\n"
            "As a corollary, for the degraded binary symmetric broadcast channel $X \\to Y_1 \\to Y_2$ "
            "with $0 \\le p_1 \\le p_2 \\le 1/2$, every single-letter pair $(I(X; Y_1 \\mid U), I(U; Y_2))$ "
            "lies inside Bergmans's boundary $\\{(h(\\alpha \\star p_1) - h(p_1), 1 - h(\\alpha \\star p_2)) : \\alpha \\in [0, 1/2]\\}$."
        ),
        "proof_notes": (
            "Proves strict monotonicity and differentiability of $h^{-1}$ on $[0, 1]$, establishes "
            "`convexOn_mglFun` via elementary derivative monotonicity of $(1 - w^2) \\operatorname{artanh}(w) / w$, "
            "deduces scalar MGL via Jensen, proves the $n$-letter vector form by induction, and derives "
            "both the single-letter Bergmans outer bound and single-letter achievability (evaluating the "
            "mutual informations at the symmetric input distribution; upgraded to the full operational "
            "capacity region in `Bridge/BroadcastCoding.lean`)."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/MrsGerber.lean", "binaryEntropy_invBinaryEntropy"),
            ("lean/InfoTheory/Bridge/MrsGerber.lean", "convexOn_mglFun"),
            ("lean/InfoTheory/Bridge/MrsGerber.lean", "mrs_gerber_scalar"),
            ("lean/InfoTheory/Bridge/MrsGerber.lean", "mrs_gerber_vector"),
            ("lean/InfoTheory/Bridge/MrsGerber.lean", "mrs_gerber_vector_cond"),
            ("lean/InfoTheory/Bridge/MrsGerber.lean", "degradedBSC_bergmans_outer_bound"),
            ("lean/InfoTheory/Bridge/MrsGerber.lean", "degradedBSC_bergmans_achievable"),
        ],
        "related_open": [
            "mrs-gerber-general",
            "broadcast-channel",
            "broadcast-channel-three-receivers",
            "degraded-message-sets-bc-three-receivers",
            "binary-skew-symmetric-bc",
            "binary-symmetric-z-interference-channel",
            "courtade-kumar",
            "primitive-relay-channel-bsc",
            "marton-inner-bound-tightness",
        ],
    },
    {
        "id": "multiuser-operational-degenerate-cases",
        "title": "Degenerate-Case Operational Capacity Regions (BC, IC, Relay, Feedback MAC)",
        "category": "ch15-network",
        "authors": "Abbas El Gamal and Young-Han Kim",
        "year": "2011",
        "reference": "El Gamal & Kim, Ch. 5, 6, 16, 17",
        "tags": ["operational-definitions", "broadcast-channel", "interference-channel", "relay-channel", "mac"],
        "statement": (
            "For channels with nonempty input alphabets, the multi-user operational capacity definitions in "
            "`InfoTheory.Core.Channels` recover the exact textbook single-user reductions in every degenerate regime:\n"
            "- **Broadcast channel** with a one-symbol receiver $Y_2$: $\\mathcal{C}_{\\mathrm{BC}}(W) = [0, C_1] \\times \\{0\\}$.\n"
            "- **Interference channel** without interference ($W_1 \\otimes W_2$): $\\mathcal{C}_{\\mathrm{IC}}(W_1 \\otimes W_2) = [0, C(W_1)] \\times [0, C(W_2)]$.\n"
            "- **Relay ignoring $X_r$** (and useless relay): $C_{\\mathrm{relay}} = C_{\\mathrm{cutset}} = C(p(y|x))$.\n"
            "- **MAC with feedback** and a silent user: $[0, C(V)] \\times \\{0\\} \\subseteq \\mathcal{C}_{\\mathrm{FB}} \\subseteq [0, \\infty) \\times \\{0\\}$ "
            "(with the matching $R_1 \\le C(V)$ converse now also proved in `Bridge/FeedbackConverse.lean`)."
        ),
        "proof_notes": (
            "Proved in `Known/Operational.lean` by reducing each multi-user error expression directly to "
            "`InfoTheory.Bridge.shannon_channel_coding_theorem` and proving causal-chain normalization "
            "`sum_causal_prod_eq_one` for feedback codes."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/Operational.lean", "bcCapacityRegion_eq_of_unique"),
            ("lean/InfoTheory/Known/Operational.lean", "icCapacityRegion_icProduct"),
            ("lean/InfoTheory/Known/Operational.lean", "relayCapacity_relayIgnoringInput"),
            ("lean/InfoTheory/Known/Operational.lean", "relayCutsetBound_relayIgnoringInput"),
            ("lean/InfoTheory/Known/Operational.lean", "Icc_prod_zero_subset_macFeedbackCapacityRegion"),
            ("lean/InfoTheory/Known/Operational.lean", "macFeedbackCapacityRegion_macIgnoringSecond_subset"),
        ],
        "related_open": [
            "broadcast-channel",
            "dm-interference-channel-capacity",
            "relay-channel",
            "mac-with-feedback",
        ],
    },
    {
        "id": "relay-channel-cutset-bound",
        "title": "Operational Cut-Set Outer Bound for the Discrete Memoryless Relay Channel",
        "category": "ch15-network",
        "authors": "Thomas M. Cover and Abbas El Gamal",
        "year": "1979",
        "reference": "Cover & Thomas, Theorem 15.10.1; El Gamal & Kim, Theorem 16.1",
        "tags": ["relay-channel", "cutset-bound", "network-it", "converse", "ch15"],
        "statement": (
            "For any discrete memoryless relay channel $W(y, y_r \\mid x, x_r)$, the operational relay "
            "capacity with strictly causal relaying obeys the single-letter cut-set upper bound:\n"
            "$$C_{\\mathrm{relay}}(W) \\le \\sup_{P(x, x_r)} \\min\\!\\big\\{ I(X; Y, Y_r \\mid X_r),\\; I(X, X_r; Y) \\big\\}.$$"
        ),
        "proof_notes": (
            "Proved directly against `InfoTheory.Core.Channels.{RelayChannel, IsRelayAchievable, "
            "relayCapacity, relayCutsetBound}`: constructs the causal relay block law `relayCodeJoint`, "
            "proves both the broadcast cut (`relay_broadcast_cut_single_letter`) and the MAC cut "
            "(`relay_mac_cut_single_letter`) at the same time-averaged input distribution `relayTimeAvgInput`, "
            "and applies Fano's inequality to establish `relayCapacity_le_cutsetBound`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/RelayCoding.lean", "relay_broadcast_cut_single_letter"),
            ("lean/InfoTheory/Bridge/RelayCoding.lean", "relay_mac_cut_single_letter"),
            ("lean/InfoTheory/Bridge/RelayCoding.lean", "relay_code_cutset_converse"),
            ("lean/InfoTheory/Bridge/RelayCoding.lean", "isRelayAchievable_le_cutsetBound"),
            ("lean/InfoTheory/Bridge/RelayCoding.lean", "relayCapacity_le_cutsetBound"),
        ],
        "related_open": [
            "relay-channel",
            "primitive-relay-channel-bsc",
            "gaussian-relay-channel-capacity",
        ],
    },
    {
        "id": "degraded-broadcast-channel-capacity",
        "title": "Superposition Coding & Operational Capacity Region of Degraded Broadcast Channels",
        "category": "ch15-network",
        "authors": "Thomas M. Cover; Patrick P. Bergmans; Robert G. Gallager",
        "year": "1974",
        "reference": "Cover & Thomas, Theorem 15.6.2 & §15.6.2; El Gamal & Kim, Theorems 5.1 & 5.2",
        "tags": ["broadcast-channel", "superposition-coding", "degraded-bc", "bergmans", "flagship", "ch15"],
        "statement": (
            "For any two-receiver discrete memoryless broadcast channel $W(y_1, y_2 \\mid x)$:\n"
            "- **Superposition Coding Inner Bound:** Every pair $(R_1, R_2) \\ge 0$ with "
            "$R_2 \\le I(U; Y_2)$, $R_1 \\le I(X; Y_1 \\mid U)$, and $R_1 + R_2 \\le I(X; Y_1)$ "
            "for some $U - X - (Y_1, Y_2)$ lies in the operational capacity region $\\mathcal{C}(W)$.\n"
            "- **Degraded BC Capacity Theorem:** Whenever $W$ is physically degraded ($X - Y_1 - Y_2$), "
            "$\\mathcal{C}(W)$ equals the closure of $\\{(R_1, R_2) \\ge 0 : R_2 \\le I(U; Y_2),\\; R_1 \\le I(X; Y_1 \\mid U)\\}$.\n"
            "- **Operational Bergmans BS-DBC:** For the binary symmetric degraded BC with crossovers "
            "$0 \\le p_1 \\le p_2 \\le 1/2$,\n"
            "$$\\mathcal{C}(\\mathrm{BS\\text{-}DBC}(p_1, p_2)) = \\{(R_1, R_2) \\ge 0 : \\exists \\alpha \\in [0, 1/2],\\; "
            "R_1 \\le h(\\alpha \\star p_1) - h(p_1),\\; R_2 \\le 1 - h(\\alpha \\star p_2)\\}.$$"
        ),
        "proof_notes": (
            "Proved directly against `InfoTheory.Core.Channels.{BroadcastChannel, IsBCAchievable, "
            "bcCapacityRegion}`: random superposition codebooks (cloud centers `u(m₂)` and conditionally "
            "i.i.d. satellites `x(m₁, m₂)`) with 2-way and 3-way joint-typicality decoding give "
            "`superpositionInnerBound_subset_bcCapacityRegion`; Gallager's converse with auxiliary "
            "$U_i = (M_2, Y_1^{i-1})$ and time-sharing gives `degradedBC_converse`; and combining "
            "`degradedBC_capacity_theorem` with `Bridge/MrsGerber.lean` proves `degradedBSC_operational_capacity_region`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/BroadcastCoding.lean", "superposition_coding_achievability"),
            ("lean/InfoTheory/Bridge/BroadcastCoding.lean", "superpositionInnerBound_subset_bcCapacityRegion"),
            ("lean/InfoTheory/Bridge/BroadcastCoding.lean", "degradedBC_converse"),
            ("lean/InfoTheory/Bridge/BroadcastCoding.lean", "degradedBC_capacity_theorem"),
            ("lean/InfoTheory/Bridge/BroadcastCoding.lean", "degradedBSC_operational_capacity_region"),
        ],
        "related_open": [
            "broadcast-channel",
            "broadcast-channel-three-receivers",
            "degraded-message-sets-bc-three-receivers",
            "marton-inner-bound-tightness",
            "binary-skew-symmetric-bc",
            "mrs-gerber-general",
        ],
    },
    {
        "id": "markov-lemma-and-wyner-ziv",
        "title": "Strong Typicality, the Markov Lemma, and the Wyner–Ziv Theorem",
        "category": "ch15-network",
        "authors": "Aaron D. Wyner and Jacob Ziv; Toby Berger",
        "year": "1976",
        "reference": "Cover & Thomas, §15.9; El Gamal & Kim, §2.4, Theorem 11.3 & Lemma 12.1",
        "tags": ["wyner-ziv", "markov-lemma", "strong-typicality", "side-information", "flagship", "ch15"],
        "statement": (
            "For a finite i.i.d. correlated source $(X, Y) \\sim P_{XY}$ and distortion $d : \\mathcal{X} \\times \\hat{\\mathcal{X}} \\to \\mathbb{R}_{\\ge 0}$, "
            "where the encoder observes only $X^n$ and the decoder observes side information $Y^n$:\n"
            "- **Markov Lemma:** If $U - X - Y$ and $(x^n, u^n)$ is $\\varepsilon_1$-strongly typical, then "
            "for $\\varepsilon_2 > \\varepsilon_1$, $(x^n, u^n, Y^n)$ is $\\varepsilon_2$-strongly typical "
            "with probability $\\ge 1 - O(1/(n(\\varepsilon_2 - \\varepsilon_1)^2))$ uniformly in $(x^n, u^n)$.\n"
            "- **Wyner–Ziv Theorem:** At every strictly feasible distortion $D > D_{\\min}$, the operational "
            "rate–distortion function with decoder side information equals\n"
            "$$R_{\\mathrm{op}}^{\\mathrm{WZ}}(D) = R_{\\mathrm{WZ}}(D) = \\inf_{\\substack{U - X - Y \\\\ \\mathbb{E}[d(X, g(U, Y))] \\le D}} I(X; U \\mid Y).$$"
        ),
        "proof_notes": (
            "Proves convexity and right-continuity of `wynerZivRateDistortion` at every strictly feasible $D$; "
            "proves `wynerZiv_converse` with auxiliary $U_i = (i, T, Y^{\\setminus i})$; builds self-contained "
            "strong typicality (`strongTypicalSet`) and `markov_lemma` via Chebyshev bounds conditioned on fixed "
            "$(x^n, u^n)$; and combines `covering_lemma_subset`, `markov_lemma`, and uniform random binning "
            "for `wynerZiv_achievability` and exact operational equality `wyner_ziv_theorem`."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/WynerZiv.lean", "markov_lemma"),
            ("lean/InfoTheory/Bridge/WynerZiv.lean", "markov_lemma_of_channel"),
            ("lean/InfoTheory/Bridge/WynerZiv.lean", "wynerZivRateDistortion_convex"),
            ("lean/InfoTheory/Bridge/WynerZiv.lean", "wynerZiv_converse"),
            ("lean/InfoTheory/Bridge/WynerZiv.lean", "wynerZiv_achievability"),
            ("lean/InfoTheory/Bridge/WynerZiv.lean", "wyner_ziv_theorem"),
        ],
        "related_open": [
            "non-asymptotic-lossy-dispersion",
            "multiterminal-source-coding",
            "ceo-problem-general",
            "gray-wyner-lossy",
            "cascade-rate-distortion-side-info",
            "universal-lossy-redundancy",
        ],
    },

    # ------------------------------------------------------------------ Entropy Region
    {
        "id": "zhang-yeung-non-shannon",
        "title": "The Copy Lemma and Zhang–Yeung Non-Shannon Information Inequality",
        "category": "entropy-region",
        "authors": "Zhen Zhang and Raymond W. Yeung",
        "year": "1998",
        "reference": "Zhang & Yeung (1998), IEEE Trans. IT; Yeung, Theorem 15.7",
        "tags": ["zhang-yeung", "copy-lemma", "non-shannon", "entropy-region"],
        "statement": (
            "Every 4-variable entropic (and almost-entropic) vector $h \\in \\operatorname{cl}(\\Gamma^*_4)$ "
            "obeys the non-Shannon information inequality\n"
            "$$2\\,I(C; D) \\le I(A; B) + I(A; C, D) + 3\\,I(C; D \\mid A) + I(C; D \\mid B).$$\n"
            "Since there exists a 4-element polymatroid violating this inequality, "
            "$\\Gamma^*_4 \\subseteq \\operatorname{cl}(\\Gamma^*_4) \\subsetneq \\Gamma_4$."
        ),
        "proof_notes": (
            "Constructs the conditional copy distribution (`copyDist`, `copyOverFirst`), copies $A$ "
            "over $(C, D)$ to form a 5-variable distribution, sums 10 Shannon submodularity inequalities, "
            "extends to $\\operatorname{cl}(\\Gamma^*_4)$ by continuity, and exhibits an explicit integer "
            "polymatroid witness where the LHS is $2$ and the RHS is $1$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "copyDist_condIndep"),
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "copyOverFirst_condIndep"),
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "zhang_yeung_entropic"),
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "zhang_yeung_almostEntropic"),
            ("lean/InfoTheory/Bridge/FeketeAndCopyLemma.lean", "almostEntropic4_ssubset_polymatroid4"),
        ],
        "related_open": [
            "entropy-region",
            "entropy-region-decidability",
            "linear-rank-entropy-region-n6",
            "network-coding-capacity-decidability",
            "secret-sharing-optimal-info-ratio",
        ],
    },
    {
        "id": "ingleton-linear-rank",
        "title": "Ingleton's Inequality for Linear Rank Vectors & Separation from Polymatroids",
        "category": "entropy-region",
        "authors": "Aubrey W. Ingleton",
        "year": "1971",
        "reference": "Ingleton (1971); Yeung, Ch. 15",
        "tags": ["ingleton", "linear-rank", "matroids", "network-coding"],
        "statement": (
            "For any four subspaces $A, B, C, D$ of a finite-dimensional vector space over any field "
            "(and hence every finite-field linear rank vector $h \\in L_4$),\n"
            "$$I(A; B) \\le I(A; B \\mid C) + I(A; B \\mid D) + I(C; D).$$\n"
            "There exists a 4-element polymatroid violating Ingleton's inequality, proving "
            "$L_4 \\subsetneq \\Gamma_4$."
        ),
        "proof_notes": (
            "Proved in `Known/EntropyRegion.lean` for arbitrary vector-space `Submodule`s via modular "
            "dimension identities, specialized to `InfoTheory.Core.Entropy.IsLinearRankVector`, and "
            "separated from `IsPolymatroid 4` by an explicit integer violator."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/EntropyRegion.lean", "ingleton_subspaces"),
            ("lean/InfoTheory/Known/EntropyRegion.lean", "ingleton_of_linearRank"),
            ("lean/InfoTheory/Known/EntropyRegion.lean", "exists_polymatroid_not_ingleton"),
            ("lean/InfoTheory/Known/EntropyRegion.lean", "exists_polymatroid_not_linearRank"),
        ],
        "related_open": [
            "linear-rank-entropy-region-n6",
            "entropy-region",
            "linear-network-coding-gap",
            "index-coding-linear-nonlinear-gap",
            "index-coding-single-letter",
            "undirected-network-coding-li-li",
            "secret-sharing-optimal-info-ratio",
        ],
    },

    # ------------------------------------------------------------------ Zero-Error & Coding
    {
        "id": "lovasz-theta-and-c5",
        "title": "Lovász Sandwich Theorem and Shannon Capacity of the 5-Cycle",
        "category": "zero-error-coding",
        "authors": "László Lovász",
        "year": "1979",
        "reference": "Lovász (1979), On the Shannon Capacity of a Graph, IEEE Trans. IT",
        "tags": ["lovasz-theta", "shannon-capacity", "c5", "zero-error"],
        "statement": (
            "For every nonempty finite simple graph $G$, the Shannon zero-error capacity $\\Theta(G)$ is bounded "
            "by the Lovász theta number:\n"
            "$$\\alpha(G) \\le \\Theta(G) \\le \\vartheta(G).$$\n"
            "For the 5-cycle $C_5$, the umbrella orthonormal representation in $\\mathbb{R}^3$ gives "
            "$\\vartheta(C_5) \\le \\sqrt{5}$, matching Shannon's 2-letter code $\\alpha(C_5 \\boxtimes C_5) \\ge 5$:\n"
            "$$\\Theta(C_5) = \\vartheta(C_5) = \\sqrt{5}.$$"
        ),
        "proof_notes": (
            "Proved end-to-end in `Known/ZeroError.lean` using Bessel's inequality for orthonormal "
            "representations, tensor-product submultiplicativity of $\\vartheta$, and Lovász's explicit "
            "3D umbrella construction for $C_5$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/ZeroError.lean", "indepNumber_le_lovaszTheta"),
            ("lean/InfoTheory/Known/ZeroError.lean", "shannonCapacity_le_lovaszTheta"),
            ("lean/InfoTheory/Known/ZeroError.lean", "lovaszTheta_cycle5"),
            ("lean/InfoTheory/Known/ZeroError.lean", "shannonCapacity_cycle5"),
        ],
        "related_open": [
            "shannon-capacity-c7",
            "shannon-capacity-complement-product",
            "shannon-capacity-union-product",
            "shannon-capacity-computability",
            "zero-error-broadcast-channel",
            "zero-error-feedback-variable-length",
        ],
    },
    {
        "id": "c7-trifferent-adder-mac-bounds",
        "title": "Classical Zero-Error Capacity Bounds: C₇, Trifferent Codes, and Adder MAC",
        "category": "zero-error-coding",
        "authors": "Claude E. Shannon; Peter Elias; László Lovász; R. Urbanke and Q. Li",
        "year": "1979",
        "reference": "Lovász (1979); Elias (1988); Urbanke–Li (1998)",
        "tags": ["c7", "trifferent", "adder-mac", "zero-error"],
        "statement": (
            "Machine-checked classical brackets on flagship open zero-error quantities:\n"
            "- **7-cycle:** $\\sqrt{10} \\le \\Theta(C_7) \\le \\vartheta(C_7) \\le \\frac{7\\cos(\\pi/7)}{1 + \\cos(\\pi/7)} < \\frac{7}{2}$.\n"
            "- **Trifferent codes:** Elias's bound $|C| \\le 2(3/2)^n$ gives $C_{\\mathrm{trif}} \\le \\log_2(3/2)$.\n"
            "- **Binary adder MAC:** $\\frac{1 + \\log_2 3}{2} \\le C_{\\mathrm{sum}}^{\\mathrm{ZEMAC}} \\le \\log_2 3$."
        ),
        "proof_notes": (
            "Proved in `Known/ZeroError.lean` and `Known/Certificates/{ShannonCapacityC7,"
            "ListDecodingZeroErrorCapacity,ZeroErrorMacAdder}.lean`, including an explicit 5D "
            "Fourier orthonormal representation for $C_7$."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/Certificates/ShannonCapacityC7.lean", "sqrt10_le_shannonCapacity_cycle7"),
            ("lean/InfoTheory/Known/Certificates/ShannonCapacityC7.lean", "lovaszTheta_cycle7_le"),
            ("lean/InfoTheory/Known/Certificates/ListDecodingZeroErrorCapacity.lean", "card_le_of_isTrifferentCode"),
            ("lean/InfoTheory/Known/Certificates/ListDecodingZeroErrorCapacity.lean", "zeroErrorList2Cap32_le"),
            ("lean/InfoTheory/Known/ZeroError.lean", "one_add_log2_three_div_two_le_zeroErrorAdderMACSumCapacity"),
            ("lean/InfoTheory/Known/ZeroError.lean", "zeroErrorAdderMACSumCapacity_le_log2_three"),
        ],
        "related_open": [
            "shannon-capacity-c7",
            "list-decoding-zero-error-capacity",
            "zero-error-mac-adder",
            "sperner-capacity-directed-graphs",
        ],
    },
    {
        "id": "classical-coding-bounds",
        "title": "Singleton, Hamming, Gilbert–Varshamov Bounds & Reed–Solomon MDS Optimality",
        "category": "zero-error-coding",
        "authors": "Richard W. Hamming; Edgar N. Gilbert; Rom R. Varshamov; Richard C. Singleton; Irving S. Reed and Gustave Solomon",
        "year": "1950",
        "reference": "MacWilliams & Sloane, Ch. 1 & 11; Cover & Thomas, Ch. 7",
        "tags": ["singleton", "hamming-bound", "gilbert-varshamov", "reed-solomon", "mds"],
        "statement": (
            "For any $q$-ary block code $C \\subseteq \\mathbb{F}_q^n$ of minimum Hamming distance $d$:\n"
            "- **Singleton bound:** $|C| \\le q^{n - d + 1}$, attained with equality by Reed–Solomon codes over $\\mathbb{F}_q$.\n"
            "- **Hamming (sphere-packing) bound:** $|C| \\cdot V_q(n, t) \\le q^n$ for $d \\ge 2t + 1$.\n"
            "- **Gilbert–Varshamov bound:** $A_q(n, d) \\ge q^n / V_q(n, d - 1)$, yielding the asymptotic "
            "binary rate bound $R(\\delta) \\ge 1 - h(\\delta)$ for $\\delta \\in (0, 1/2)$."
        ),
        "proof_notes": (
            "All five classical coding-theory theorems are proved directly against `InfoTheory.Core.Coding` "
            "in `Known/Coding.lean` (reusing Mathlib's `Hamming` metric via `Bridge/Mathlib.lean` and "
            "`Polynomial.roots` for Reed–Solomon MDS distance)."
        ),
        "lean_decls": [
            ("lean/InfoTheory/Known/Coding.lean", "singleton_bound"),
            ("lean/InfoTheory/Known/Coding.lean", "hamming_bound"),
            ("lean/InfoTheory/Known/Coding.lean", "gilbert_varshamov_bound"),
            ("lean/InfoTheory/Known/Coding.lean", "gilbertVarshamov_le_asymptoticCodeRate"),
            ("lean/InfoTheory/Known/Coding.lean", "reedSolomon_isLinearMDSCode"),
        ],
        "related_open": [
            "gilbert-varshamov-binary",
            "mds-conjecture",
            "list-decoding-capacity-binary-linear",
            "explicit-list-decodable-binary",
            "edit-distance-code-capacity",
            "batch-codes-optimal-redundancy",
            "locally-decodable-codes-3-query",
            "locally-correctable-codes-constant-rate",
        ],
        "analogous_open": [
            "kissing-number-high-dim",
        ],
    },
]
