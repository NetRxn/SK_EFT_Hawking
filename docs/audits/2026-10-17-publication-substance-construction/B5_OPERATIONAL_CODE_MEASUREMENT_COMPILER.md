# B5: operational Steane code, adaptive compilation and a composed accuracy theorem

Author: publication_checkpoint_source. Original manual construction, 2026-10-18.
Status: Independently accepted scoped manual operational milestone; [complete original independent review](reviews/B5_OPERATIONAL_CODE_MEASUREMENT_COMPILER.md), reviewer publication_b6_fdt_review, SHA256 e72fcb7fd42007496581b3db66072a3f70c730ceba0002d6b18914b4584aedfd; lead acceptance36697ad96e87f437222bec9273ac66997750e4b1a6ecc02f3632b518a027c4f4. This is the ideal-control independent-storage theorem, not full noisy-gadget/native/physical B5 completion. The all-real mathematical selector is distinct from the effective compiler, whose target entries AND positive tolerance require certified computable representations. Original review-packet B4 parent metadata is a retained administrative mismatch, not the scientific parent or a new B4 result.

## 1. Original objective and the theorem actually constructed

The original B5/D6 objective remains the composite code → measurement → compiler → universal-logic theorem on the program's intended substrate. Density together with an unrelated real recursion is insufficient. We construct the finite operators and the semantic chain, including a nonzero noise instance, rather than add the desired equality as a record field.

The complete result below has a precisely specified operational domain: encoded finite adaptive quantum circuits; ideal encoders, controls, syndrome extraction, correction, preparation, measurement and classical feed-forward; and independent stochastic one-qubit storage faults between those ideal operations. For this domain we derive Steane's distance three and arbitrary one-qubit correction, give an actual T-injection instrument, prove density of the actual H/T/CNOT alphabet, specify a terminating mathematical compiler, and prove a reference-stable accuracy bound with a circuit-length-dependent concatenation level. Its all-pairs coefficient is 21, derived here for a seven-child memory block. It is not the AGP CNOT coefficient 35,235.

This is a substantive operational special case and composition primitive for the original objective. It is not full noisy-gate fault tolerance, an AGP gadget enumeration, a Fibonacci-braid implementation, a physical noise identification, a native Lean theorem, or full B5 completion. Section 15 gives the concrete outstanding construction and the failed naive attempt; these are retained parts of the original objective.

## 2. Finite systems, channels, references and adaptive semantics

Let H_n=(C²)^{⊗n}, with the ordered computational basis indexed by binary words. States are positive matrices of trace one, unnormalized branches are positive matrices of trace at most one, and ||.||_1 is the sum of singular values. A finite channel has Kraus operators K_a with Σ_a K_a†K_a=I. This definition allows different finite input/output dimensions. Complete positivity follows by tensoring each K_a with an arbitrary finite identity; trace preservation is the displayed sum.

A finite instrument has operators K_{m,a}, with Σ_{m,a} K_{m,a}†K_{m,a}=I. Its output is Σ_m |m><m|⊗Σ_a K_{m,a}ρK_{m,a}†, including zero branches. No division by outcome probability occurs. An adaptive program is a finite typed tree of unitary gates on named wires, preparations, computational-basis instruments, discards, and branches controlled by stored classical outcomes. The leaf output contains the declared classical record and the live quantum wires. Ancillas can be padded to a common finite width and halted branches to a common finite number of steps.

The denotation is defined recursively by these matrix formulas, composition and classical direct sum. It is a CPTP map: induction multiplies Kraus operators along a branch; the sums of K†K telescope backwards to I, and controlled continuations preserve the trace of each unnormalized branch. A discard has Kraus <j| on the discarded factor; preparation of |ψ> has Kraus |ψ> (or |ψ><j| for reset). Z measurement has projectors |0><0|, |1><1|. These are actual operations, not semantic-equality hypotheses.

For channels Φ,Ψ with common input and output, define
  d_ref(Φ,Ψ)=sup_{r≥1, ρ state on input⊗C^r}
                 (1/2)||((Φ-Ψ)⊗id_r)(ρ)||_1.                 (2.1)
This stabilized state distance is our error convention. It lies in [0,1]. We do not require a native theorem identifying different library definitions of the diamond norm. All bounds here hold for every finite reference dimension, and hence also for the input-sized stabilization used by the inspected source.

A CPTP map contracts trace norm on Hermitian matrices: write X=X_+-X_- by the spectral theorem, then positivity, the triangle inequality and trace preservation give ||Φ(X)||_1≤tr X_++tr X_-=||X||_1. The same proof holds after every finite spectator lift. Precomposition takes a state to a state, so d_ref is contractive under both channel precomposition and postcomposition. Its triangle inequality is immediate from the trace-norm triangle inequality. Classical direct sums have trace norm equal to the sum of their block trace norms. These facts justify controlled continuations and telescoping through adaptive steps without normalizing rare branches.

For unitaries U,V, add and subtract VρU†:
  UρU†-VρV†=(U-V)ρU†+Vρ(U-V)†.
The trace/operator Hölder inequality and ||U||=||V||=1 give
  d_ref(Ad_U,Ad_V)≤||U-V||_op.                              (2.2)
Tensoring with a spectator preserves the operator norm. A scalar phase of modulus one cancels from Ad, so the right side may be minimized over such phases if useful. We will never replace a coherently controlled relative phase by a global phase.

Finally a terminal instrument/measurement is a channel. For its classical probabilities p_m,q_m, (1/2)Σ_m|p_m-q_m|≤d_ref(Φ,Ψ). Consequently every declared output event differs in probability by at most this error, even with an entangled reference. No claim about normalized postselected states follows without a probability lower bound.

## 3. Actual Steane CSS Hilbert-space encoding

All binary arithmetic in this section is over F_2. Use exactly the source's parity-check rows:
  h_1=0001111, h_2=0110011, h_3=1010101.
The seven columns of H, in this order, are 001,010,011,100,101,110,111.

Let D be their row span. The rows are independent (columns 100,010,001 isolate their coefficients), each has weight four, and any two distinct rows have overlap two. Thus D⊆D^⊥ and dim D=3. Here are all eight elements:
  0000000, 0001111, 0110011, 1010101,
  0111100, 1011010, 1100110, 1101001.                         (3.1)
Every nonzero element has weight four, also seen by evaluating a nonzero linear functional on the seven nonzero columns. Put j=1111111. It is orthogonal to D and is not in D, by its odd weight. Dimension four then gives
  C:=ker H=D^⊥=D⊕span{j}.

Define actual vectors, not just code parameters:
  |0_L>=8^{-1/2}Σ_{u∈D}|u>,
  |1_L>=8^{-1/2}Σ_{u∈D}|u+j>,
  V|b>=|b_L>.                                               (3.2)
The two cosets are disjoint; each sum has eight distinct basis terms. Thus V†V=I_2, E(ρ)=VρV† is a channel, and P=VV† has rank two.

Use X|b>=|b+1>, Z|b>=(-1)^b|b>, Y=iXZ. On seven qubits X^uZ^v acts in that order, with all complex phases retained. The six Hermitian stabilizers X^{h_a},Z^{h_a} commute because h_a·h_b=0. The first three stabilize (3.2) by translations of D; the latter stabilize them by orthogonality. Their joint +1 eigenspace is exactly span{|0_L>,|1_L>}: Z constraints force the basis support into C; X translations force equal coefficients within each D-coset. Hence
  P=Π_{a=1}^3 (I+X^{h_a})/2 · Π_{a=1}^3 (I+Z^{h_a})/2.       (3.3)
This also proves that the chosen signs exclude -I from the stabilizer and that no extra logical dimension has been introduced.

The physical X^j exchanges the two vectors, and Z^j acts as (-1)^b: u has even weight and u+j odd weight. They implement the actual logical X and Z, including their anticommutation.

## 4. Distance three and a full syndrome decoder

A Pauli X^uZ^v commutes with every stabilizer exactly when Hu=Hv=0. A nonzero binary word of weight one or two cannot be in ker H: one nonzero column cannot sum to zero, and two different nonzero columns cannot sum to zero. Therefore every nonidentity Pauli of total support at most two has a nonzero syndrome (at least one of u,v is nonzero and has weight at most two). It cannot preserve the codespace, so it is neither a nontrivial logical Pauli nor a scalar logical action.

The word f=1110000 satisfies Hf=001+010+011=0 and has odd weight three. It is not in D; indeed Z^f acts on (3.2) as (-1)^b, since f·D=0 and f·j=1. It is a nontrivial logical Z of weight three. The minimum support of a nontrivial normalizing Pauli is consequently exactly three. This derives [[7,1,3]] from the operators; it does not use the stored d=3 field.

Order a syndrome as s=(s_X,s_Z)∈F_2³×F_2³, where the six measured eigenvalues are (-1)^{s_X,a},(-1)^{s_Z,a}. The syndrome of X^uZ^v is (Hv,Hu). Let
  P_s=Π_a (I+(-1)^{s_X,a}X^{h_a})/2
          ·Π_a (I+(-1)^{s_Z,a}Z^{h_a})/2.                   (4.1)
These are mutually orthogonal projectors and Σ_s P_s=I.

For t∈F_2³ let e(t)=0 if t=0, and otherwise let e(t) be the unit vector at the unique column of H equal to t. Choose
  W_s=X^{e(s_Z)}Z^{e(s_X)}.
Its syndrome is s; it takes P's range unitarily onto P_s's range, as follows by commuting it through each projector. Thus each P_s has rank two and P_s=W_s P W_s†.

The decoder has the 64 explicit rectangular Kraus operators
  R_s=V†W_s†P_s : H_7→C²,
  D_1(σ)=Σ_s R_s σ R_s†.                                   (4.2)
Because R_s†R_s=P_s W_s P W_s†P_s=P_s, Σ_s R_s†R_s=I_128. It is CPTP on the entire physical Hilbert space, not merely on a promised good-error subspace. The encoded recovery is E∘D_1. Sequential measurements of the commuting six stabilizers realize (4.1); applying W_s† and then the decoder realizes (4.2). Corrections for the 42 syndrome values not occupied by I and weight-one Paulis are still defined, so the channel is total.

The 22 errors I,X_i,Y_i,Z_i have distinct syndromes:
  I:(0,0), X_i:(0,h_i^col), Z_i:(h_i^col,0),
  Y_i:(h_i^col,h_i^col).                                   (4.3)
For each such error F_a and every syndrome s,
  R_s F_a V=δ_{s,s(a)} c_a I_2, |c_a|=1.                   (4.4)
For Y, W_s=X_iZ_i=-iY_i, so the correction scalar includes i; it does not change any density matrix. Formula (4.4) follows from orthogonal syndrome projectors and W_s†F_a being the indicated scalar, not from a claim that projective Pauli labels commute.

Now let a channel's every Kraus operator be in span{I,X_i,Y_i,Z_i:1≤i≤7}. Expanding K_α=Σ_a c_{αa}F_a and using (4.4) yields
  D_1(K_α VρV† K_α†)=Σ_a |c_{αa}|²ρ.
Summing α gives ρ: trace preservation applied to an encoded trace-one state forces Σ_{αa}|c_{αa}|²=1. All off-diagonal error terms vanished by distinct syndromes. The same operator calculation with I_R tensored on proves
  (D_1⊗id_R)(N⊗id_R)((V⊗I_R)ρ(V†⊗I_R))=ρ               (4.5)
for every finite entangled reference. In particular this corrects an arbitrary one-qubit CPTP error at any one unknown site, since its 2×2 Kraus operators expand in I,X,Y,Z. It also corrects coherent errors whose Kraus operators lie in the full 22-dimensional span; no independent classical bit-flip assumption was used in this correction theorem.

## 5. Actual logical gates and logical measurement

H=2^{-1/2}[[1,1],[1,-1]], S=diag(1,i), T=diag(1,ω), ω=e^{iπ/4}, and CNOT|x,y>=|x,y+x>. These specify the matrices and chronological gate convention.

The sevenfold transversal Hadamard satisfies H^{⊗7}V=VH. To verify it, Fourier transform (3.2). The coefficient sum Σ_{u∈D}(-1)^{u·x} is eight for x∈D^⊥ and zero otherwise; the extra j phase for b=1 is (-1)^{j·x}. Splitting C=D∪(D+j), with j·D=0 and j·j=1, gives precisely (|0_L>+(-1)^b|1_L>)/sqrt2.

S^{⊗7}V=VS†: every term of |0_L> has weight 0 or4 and phase one; every term of |1_L> has weight 7 or3 and phase -i. Thus (S†)^{⊗7}V=VS, and this opposite physical orientation matters. A transversal CNOT sends the two code cosets (u+bj,v+cj) to (u+bj,u+v+(b+c)j); the change (u,v)↦(u,u+v) is a bijection of D². It therefore satisfies
  CNOT^{⊗7}(V⊗V)=(V⊗V)CNOT.                               (5.1)

Logical Z measurement may use projectors Q_b=(I+(-1)^b Z^j)/2. On code states Q_b V=V|b><b|. This realizes the nondestructive logical instrument; a discard of the measured quantum block gives the destructive one. All outcome branches are unnormalized and remain correct with a reference. Alternatively measuring all seven physical Z bits and recording their parity gives the same classical probabilities; it is not the same quantum output instrument if those fine-grained outcomes are retained. We use Q_b when promising the logical instrument.

A unitary U on k logical wires has a concrete extension to the full physical space:
  U_bar=V^{⊗k}U(V†)^{⊗k}+(I-P^{⊗k}).                      (5.2)
The two summands act on orthogonal reducing subspaces, so U_bar is unitary and U_bar V^{⊗k}=V^{⊗k}U. This supplies an actual total extension where needed, not an assumed semantic equality. Equation (5.2) is a possibly highly nonlocal ideal operation, with no claim of a bounded-arity fault-tolerant implementation. For H,S,CNOT, (5.1) and its counterparts give explicit transversal alternatives at level one.

## 6. Adaptive T injection, with branch matrices

Prepare the actual logical magic state |A>=T|+>=(|0>+ω|1>)/sqrt2, encode it by V, and use the transversal logical CNOT with the data as control and magic ancilla as target. Measure the ancilla in logical Z. For data α|0>+β|1>, the two unnormalized data vectors before correction are
  outcome0: (α|0>+ωβ|1>)/sqrt2,
  outcome1: (ωα|0>+β|1>)/sqrt2.
The corresponding matrices are
  K_0=T/sqrt2, K_1=diag(ω,1)/sqrt2=ω T†/sqrt2.
Apply S to the data only in branch1. Since ST†=T, the corrected matrices are
  L_0=T/sqrt2, L_1=ω T/sqrt2.                               (6.1)
Thus L_m†L_m=I/2, Σ_m L_m†L_m=I, and each corrected branch is (1/2)TρT†, also on data entangled with any reference. The coin is exactly uniform and independent of the input/reference. Discarding this internal coin gives Ad_T; retaining it corresponds to Ad_T followed by an independent fair classical bit. Target semantics must make this choice explicitly.

At level one, ideal |A_L>=V|A>, transversal CNOT, Q_m, and the conditional transversal physical S† implement (6.1). This is an actual encoding/measurement/feed-forward construction. It does not derive |A_L> from noisy stabilizer preparations or prove magic-state distillation. Preparation of |A_L> is one of this theorem's explicitly ideal resources.

H^{-1}=H. Implement T^{-1} by seven successive T injections, since T^8=I. S itself is already realized above. Consequently every signed H/T/CNOT word has an exact finite adaptive encoded implementation. No T-transversality was assumed; indeed the code is not invariant under T^{⊗7}: on |0_L> the seven nonzero D terms acquire -1 while the zero term does not.

For carrying examples, (6.1) can be checked on |0>,|1>,|+> and on the Bell state. The Bell input produces (|00>+ω|11>)/sqrt2 after correcting either outcome. This last control exposes preservation of off-diagonal phase and correlations, which a classical bit-recovery argument would not establish.

## 7. Finite concatenated encoding and recovery

Put V_0=I_2 and V_{l+1}=(V_l)^{⊗7}V, an explicit isometry C²→(C²)^{⊗7^{l+1}}. Define the full decoder recursively:
  D_0=id,
  D_{l+1}=D_1 ∘ (D_l)^{⊗7}.                               (7.1)
Every map is CPTP. D_l E_l=id, by induction, where E_l=Ad_{V_l}. The restoring recovery is E_l∘D_l, and always returns a state in the level-l codespace. There is no promise on the input to D_l.

Every ideal logical operation at level l can be defined by (5.2), with V_l replacing V, or by the encoded instrument formulas and ideal state preparations already given. Composition then gives the adaptive semantics by literal matrix substitution. These are total finite operations even at arbitrarily large l. They do not purport to be circuits of noisy elementary one/two-qubit devices. The recursive decoder and encoders are explicitly ideal in this model.

A recursive decoder contains t_l=(7^l-1)/6 instances of D_1: t_0=0 and t_{l+1}=1+7t_l. A restoring re-encoding uses the same number of elementary V nodes. This supplies a finite semantic resource count; it is not an experimental device cost.

## 8. A concrete nonzero stochastic storage-noise model

Fix 0≤p≤1. In each storage interval and at each physical leaf qubit take independent Bernoulli flags. On flag0 apply identity; on flag1 apply a specified one-qubit CPTP channel B_i. For a fully explicit example take B_i=Ad_Z for every leaf. A finite interval with K leaves has sample space {0,1}^K and
  μ(ω)=p^{|ω|}(1-p)^{K-|ω|}.
Summing over all flags gives (p+(1-p))^K=1; p=0,1 have their usual degenerate point-mass meanings. Summing over unconstrained coordinates proves the exact cylinder probability p^{|S|}. This is an actual finite probability law, not a function merely named a probability.

For any fixed flag pattern, the physical operation is a product of channels, so conditioning on that pattern is a well-defined CPTP channel independent of the input. Define a level0 node bad iff its flag is1; recursively define a parent bad iff at least two of its seven children are bad. These are pessimistic structural events, not assertions that every bad pattern necessarily causes a logical error.

We derive good ⇒ correct. At l=0 a good flag is identity. At a level-(l+1) good parent, at least six of the seven decoded child channels are exactly identity by induction; the optional seventh is a one-qubit CPTP channel because D_l and E_l are CPTP. The conditional leaf channel factors across these seven children. Equation (4.5) therefore says that the outer D_1 corrects it exactly, with any reference. This proves, from the actual channels and code,
  D_l N_{ω,l} E_l=id for every good flag pattern ω.           (8.1)
Here N_{ω,l} is the product leaf-storage channel for that pattern. Its extension with a reference is included. Equation (8.1) is the derived carrying statement; it was not an added field or input hypothesis.

Sibling bad events depend on disjoint leaf flags and are independent. If r_l is their probability, their parent has
  r_{l+1}=1-(1-r_l)^7-7r_l(1-r_l)^6
         ≤ C(7,2) r_l²=21r_l², r_0=p.                     (8.2)
The inequality is the union bound over all 21 unordered pairs. Every pattern with at least two bad children contains a pair, including patterns with three through seven bad children. Thus higher fault sets are covered here by a proved all-pairs structural statement. No pair was dropped because it happened to be benign in a two-fault-only experiment.

Let q_0=p and q_{l+1}=21q_l². Induction using (8.2) gives r_l≤q_l, and direct induction gives
  q_l=(21p)^{2^l}/21.                                      (8.3)
This algebraic expression may exceed one above threshold; it is an upper bound, not then an exact probability. When 21p<1 it tends to zero. No claim identifies 1/21 with a noisy-gate/device threshold.

Averaging the conditional channels after decoding, (8.1) gives
  D_l N_l E_l=(1-r_l)id+r_l B_l,                            (8.4)
where B_l is the average of the finitely many bad-pattern CPTP channels when r_l>0. If r_l=0 choose any channel for B_l. Consequently
  d_ref(D_l N_l E_l,id)≤r_l≤q_l.                           (8.5)
The trace-distance factor is r_l, not 2r_l, because (2.1) includes one half. Re-encoding preserves this bound on encoded inputs. The environment/reference cannot invalidate (8.4), since each good channel is exactly identity with the reference and the classical weights do not depend on the input.

This construction is nonvacuous. For 0<p<1 the base flags have genuinely positive nonunit probability; r_1≥p²(1-p)^5>0. With Z faults at sites1 and2, syndrome points to site3 and recovery leaves Z^{1110000}, the nontrivial logical Z in Section4. Thus there are actual logical failures, not merely nonempty named events. The exact probability of the pattern with just those two flags is p²(1-p)^5>0.

## 9. Literal H/T/CNOT syntax is universal: a manual density proof

We establish the approximation supply without assuming an LDP, desired compiler correctness, a density record field, or any formal API availability.

Use the SU(2) phase representatives h=iH and t=diag(e^{-iπ/8},e^{iπ/8}); their channels are exactly H and T. Let c=cos(π/8), s=sin(π/8). Pauli multiplication gives
  ht=(s/sqrt2)I+(i/sqrt2)(cX-sY+cZ).
If its eigenvalues are e^{±iθ}, then (2cosθ)²=2s²=1-1/sqrt2. This is not an algebraic integer: in Q(sqrt2) its conjugates multiply to 1/2; the norm of an algebraic integer is a rational algebraic integer and thus an integer. If θ/π were rational, the eigenvalues would be roots of unity, their sum 2cosθ and its square algebraic integers, a contradiction. Hence θ/π is irrational.

The powers of e^{iθ} are dense on the circle. One elementary proof partitions the circle into M equal intervals, finds by pigeonhole a nonzero power within 2π/M of1, and uses successive multiples of that small angle to approximate any angle; taking M→∞ proves density (irrationality prevents a zero step). Therefore the closure G of the group generated by h,t contains the entire circle exp(iu n·σ), where n is proportional to (c,-s,c). Conjugating by t gives another full circle with axis m equal to n rotated about Z by π/4 up to orientation. n has both nonzero Z and nonzero transverse components; thus m is neither parallel nor antiparallel to n.

Conjugate the m-circle by exp(iπ n·σ/4). Its axis m' is the rotation of m by a right angle about n, up to orientation. The three vectors n,m,m' are independent: their perpendicular-to-n components are a nonzero vector and its quarter-turn. The map
  (a,b,d)↦exp(ia n·σ) exp(ib m·σ) exp(id m'·σ)
has at zero the invertible derivative (a,b,d)↦i(a n+b m+d m')·σ. The ordinary finite-dimensional inverse function theorem in a local SU(2) matrix chart gives a neighborhood of I contained in G. A subgroup containing a neighborhood is open. SU(2), the unit three-sphere through its usual Pauli coordinates, is connected; its open subgroup has open cosets and must be all of SU(2). This proves density of the actual signed H/T alphabet up to irrelevant global channel phase.

For n≥2 adjoin CNOT on any ordered pair. The closure contains every local exp(iu P_i) for P_i=X,Y,Z. It contains exp(iu Z_{i_1}...Z_{i_k}): conjugate exp(iu Z_{i_k}) by CNOTs with the other support wires as controls and i_k as target, using
  CNOT_{a,b} Z_b CNOT_{a,b}=Z_a Z_b.
Conjugating individual factors by local H and S rotations gives exp(iu P) for every nonidentity tensor Pauli P. The iP form a real basis of su(2^n): Pauli words are orthogonal under tr(PQ), there are 4^n of them including I, and traceless anti-Hermitian matrices have real dimension 4^n-1. Products of these 4^n-1 one-parameter groups have an invertible derivative at zero. The same inverse-function argument supplies a neighborhood of I in SU(2^n).

For completeness SU(d) is connected: diagonalize a unitary, choose real eigenangles and alter one by an integer multiple of2π so that their sum is zero; conjugating diag(e^{itα_j}) gives a path from I to the unitary inside SU(d). Hence the subgroup closure is SU(2^n). Phase choices for CNOT do not alter conjugation or any channel: for n=2 multiply its matrix by e^{iπ/4} to get determinant1; for n≥3 its determinant is already1. An arbitrary U(d) target may be made special-unitary by a scalar phase, which leaves its unconditioned channel unchanged.

This proves finite-dimensional universal quantum logic. It does not prove any physical braid matrices equal these gates, or their preservation of a particular anyon fusion encoding.

## 10. A finite compiler, rather than an uninterpreted witness

For a fixed width n enumerate all signed words over named H_i,T_i,CNOT_{i,j}, first by length then lexicographically. For synthesis evaluate each letter using the SU phase representatives of Section9: h_i=iH_i, t_i=e^{-iπ/8}T_i, and the determinant-corrected CNOT (multiply by e^{iπ/4} for n=2; no correction for n≥3). These are scalar phases of the full-register textbook matrices. Inverses use the inverses of those representatives. Chronological synthesis syntax [g_1,...,g_m] denotes W_word=W_{g_m}...W_{g_1}. The textbook physical word has exactly the same channel as W_word, because their total difference is one scalar global phase. Physical CNOT is self-inverse; its corrected inverse is represented by the same physical CNOT with the opposite global phase. A mathematical compiler for target U∈SU(2^n) and η>0 returns the first word with ||W_word-U||_op<η. Section9 proves that the set is nonempty; well-ordering makes the first word defined and finite. This construction explicitly depends on the proved density of actual matrices. It is not a newly assumed semantic-equality field.

For arbitrary real input entries this is a mathematical, potentially noncomputable compiler, as are some inspected source definitions. There is a genuine terminating semidecision version for computable target entries supplied with certified rational approximation oracles: dovetail pairs (word,precision), enclose every matrix entry of W_word-U, and accept a rational upper bound on its Frobenius norm strictly below η. The correct bound is Σ|entry|² with complex conjugation, not Σ entry². Since ||A||_op≤||A||_F≤sqrt(d)||A||_op, density supplies a word with ||A||_op<η/(2sqrt(d)). Its Frobenius norm is <η/2, so sufficiently fine entry enclosures certify <η. Enumeration eventually visits that finite word and that precision. All accepted words satisfy the operator error contract. No such compiler was executed in this task.

This proves finite termination, not a polylogarithmic runtime or optimal word length. Let m be the actual finite output length. It is counted after compilation and is the length used in the noise budget; a recursion-level count unconnected to m would not suffice.

For a finite adaptive target over arbitrary one-qubit unitaries, CNOT, preparations and computational measurements, compile each one-qubit gate independently with accuracy η. For a U(2) gate choose a determinant-one phase representative. The error at that occurrence is ≤η by (2.2). Finite induction on the tree, or padding it to a controlled finite schedule, gives total approximation error at most rη, where r is the total number of such gate nodes in the finite tree (a conservative bound on the number on any branch). This bound includes the quantum output and the declared classical record. Classical control is essential: phase representatives must not be substituted into a coherently controlled-U operation without preserving its relative phase. Such a target can instead be compiled as an entire larger unitary by the general n-qubit construction above.

A source compiler output in a free group can be realized as its explicit reduced signed word. Check its multiplication convention: the source braid foldl product multiplies matrices in list order, whereas our list is chronological, so an order-reversing conversion is required if matrices act on column vectors and that source list is consumed directly. The signed SU(2) representatives h,t differ from textbook H,T only by global phases; interpreting their free word gives the same channel as our textbook word, including inverses. No anyon/qubit/qutrit dimension identification is automatic.

## 11. Exact encoded compilation of a finite word

Replace each H by its encoded H operation, each T by the four-step gadget (magic preparation, CNOT, measurement, conditional S), each T^{-1} by seven such gadgets, and each CNOT by its encoded CNOT. The guarded correction step is present as a time slot even when its branch applies identity. Preparations, logical Z instruments and discards have the formulas already given; use an extra encoded ancilla register for T and discard/reset it before reuse.

At level1 these encoded H,S,CNOT operations have the transversals proven in Section5. At any finite level use (5.2) and the corresponding encoded instruments with V_l, or derive matching concatenated transversals separately. We rely on the explicit ideal extensions, not an unstated concatenated-gadget fault theorem.

For every ideal gadget branch its Kraus action on the encoded subspace is the logical branch action under V_l. In particular (6.1) gives a fair independent internal coin and Ad_T after forgetting that coin. Substitution into the adaptive Kraus-path semantics proves by induction
  D_out ∘ [[encoded compilation of w]] ∘ E_in = [[w]],        (11.1)
with the declared internal coins forgotten. D_out denotes D_l on the live output blocks; classical outcomes are carried identically. The induction multiplies the derived primitive Kraus identities; (11.1) is a conclusion, not a supplied compiler specification.

For a word of m signed H/T/CNOT letters there are at most 28m primitive time slots: H and CNOT need one, T needs four, T^{-1} needs28. Add the target program's preparation and measurement slots and use a conservative finite bound N on every adaptive path. Padding halted paths gives exactly N slots. For a fixed n-wire target, one extra live encoded magic block suffices, so w=n+1 is a width bound (or choose the larger finite width demanded by a target's own ancillas). Preparation/discard may reduce live width; using w remains conservative. Set N≥1 by an identity slot if necessary.

## 12. Noisy composed semantics and explicit level choice

Before each of those N ideal primitive slots, apply independent leaf-storage noise to every live encoded block, followed by the ideal restoring recovery E_lD_l. The flag distribution is fresh between slots and blocks; all controls and recovery are ideal. This specifies exactly which operations may fail. There are at most Nw blocks of storage locations, each with 7^l physical leaf flags.

On encoded states a block's decoded noise differs from id by at most q_l, with arbitrary reference, by (8.5). A w-block product noise differs from identity by at most wq_l, by replacing factors one at a time and using contractivity. Insert those channels into the fixed padded controlled schedule. A telescoping replacement of one noisy slot by its ideal slot, carrying both the classical memory and all other wires as a reference, proves
  d_ref(decoded noisy compiled program, ideal target)
        ≤ α + Nw q_l,                                     (12.1)
where α is the ideal compiler error, e.g. rη. Equivalently, the event that any structural bad storage block occurs has probability ≤Nw r_l; on its complement literal Kraus-path substitution gives the ideal program, which also bounds the noise contribution. This alternative uses fresh input-independent flags and does not condition on the adaptive measurement results. Neither proof assumes independence of overlapping ex-Recs.

Given ε∈(0,1), choose η=ε/(4 max{1,r}) for the finite target-tree construction, so α≤ε/4. Compile first, expand the actual signed words, and determine finite N,w as above. For 0<p<1/21 put λ=ln(1/(21p))>0 and choose
  B=max{1, ln(2Nw/(21ε))/λ},
  l=max{1, ceil(log_2 B)}.                                 (12.2)
Then 2^l≥B and
  Nw q_l=(Nw/21) exp(-λ2^l)≤ε/2.
Equation (12.1) is therefore <ε. For p=0 take l=1 and the noise contribution is zero. The formula is not used at or above p=1/21; no contraction is claimed there. If the target is already an exact word, take α=0 and use the same noise allocation. Width and count must include any target ancillas and all injection slots.

Physical encoded width is at most w7^l. The storage-flag count is at most Nw7^l, and ideal recursive decode and re-encode use at most 2Nw(7^l-1)/6 one-level nodes. These finite formulas count the specified idealized operations, not noisy bounded-arity hardware gates. For fixed p<1/21, (12.2) implies 7^l grows as a power of log(Nw/ε), up to constants depending on p; this is a statement about the chosen memory level only. Our enumeration compiler has no polynomial or polylogarithmic time guarantee.

This is the composed operational theorem: actual finite code and recovery + actual adaptive compiler semantics + a derived nonzero-noise model give a target-channel and output-measurement accuracy bound for universal finite logic, with level chosen after word growth is accounted for. Its ideal-control hypothesis is indispensable.

## 13. Carrying circuits and countercontrols

1. **One-error quantum correction.** For any |ψ> possibly entangled with R, encode it by V. An X at site with column101 produces syndrome (000,101); the correction is that X. A Z there produces (101,000); a Y produces (101,101), with the phase treated in (4.4). Arbitrary linear combinations and one-qubit channels follow from the Kraus calculation, not from testing only basis states.

2. **A real nontrivial logical fault.** Z at sites1,2 gives syndrome (011,000); the chosen correction is Z at site3, leaving Z_1Z_2Z_3. It fixes |0_L> and negates |1_L>, and flips |+_L> to |-_L>. Thus treating every two-error pattern as corrected would be false. The event has positive probability p²(1-p)^5 in the explicit noise model.

3. **Universal-word carrying example with phase-sensitive measurement.** Starting with already supplied |00>, execute H_1; T_1; CNOT_{1,2}; H_1; H_2; measure Z_1,Z_2. Before the last Hadamards the state is (|00>+ω|11>)/sqrt2. The final parity expectation is <X⊗X>=Re ω=1/sqrt2, so
     P[even parity]=(1+1/sqrt2)/2.
   Expand T into its four slots. The schedule has ten slots: the initial H, four injection slots, CNOT, two final H gates and two measurements. w=3 is sufficient. With p=1/210 and l=2, 21p=1/10 and q_2=1/210000; the total noise error is ≤30/210000=1/7000. The stated event probability is therefore within 1/7000 of its ideal value. Initial preparation was supplied as input; if charging two preparation slots as well, use N=12 and the bound36/210000=3/17500. These are manual rational consequences, not executed simulations.

4. **A conjunction cannot certify a circuit.** An abstract dense ideal alphabet and a scalar sequence can coexist with an implemented device that resets every input to |0>. On input |1> its identity-target error is one. Density and A q_l<1 say nothing that excludes that device. Equations (4.5), (6.1), (8.1), (11.1) and (12.1) are the missing carrying statements.

5. **Distance is not fault containment.** Extract a Z-parity stabilizer using an ancilla target and sequential data→ancilla CNOTs. A Z fault on that target after the first coupling propagates backwards through the remaining couplings as Z faults on multiple data qubits, since CNOT conjugates Z_target to Z_control Z_target. A single extraction fault can therefore exceed the one-error correction radius. A distance-three field, and even our proved distance-three code, does not prove this unverified gadget fault tolerant.

6. **Pair counts and correlated faults.** If all leaf flags are one shared Bernoulli flag, each leaf marginal is p but a pair fails with probability p rather than p². This destroys (8.2). Likewise two recursive rectangles sharing leaves do not have independent bad events merely because distinct physical leaf flags are independent. Our proof uses disjoint sibling leaves and fresh storage intervals. It does not transfer that argument to overlapping AGP ex-Recs.

7. **Higher fault sets.** A list identifying all malignant pairs under exactly two faults does not exclude a minimal malignant triple with no malignant pair. Our Section8 uses every pair and proves good implies correct, so its event coverage is valid at every weight. An AGP refinement retaining only35,235 pairs needs the additional structural/cubic/acceptance analysis of its actual gadgets; we have not supplied it by naming a count.

## 14. What the inspected source actually supplies

These are static source observations, not current native execution, library-availability or kernel-closure receipts.

* FaultTolerance/Basic.lean has projective Pauli labels (phase-forgetting multiplication), a weight count, location labels and Clifford operation labels. They are useful syntax; they do not denote our matrices or channels by themselves.
* StabilizerCode.lean records n,k,d, generator and logical-operator list lengths and distance_pos. SteaneCode.lean supplies the same H as Section3 and six generator masks, with d:=3 and its distance-three theorem a reflexive parameter check. Sections3–4 provide the missing manual operator proof, not a claim that this proof has been installed.
* ExRec.lean is a positive location count. MalignantPairAttestation is a number A with A≤choose(M,2). Counting.lean pins M_CNOT=575 and A_CNOT=35235 and proves their combinatorial well-formedness. This does not enumerate physical fault effects or prove good implies correct.
* MalignantUnionBound.lean really proves bounds for measures of finite unions of intersections. ConcatenatedComposition.lean really derives level bounds on actual event measures under hbase, hcard≤A, hstruct and hsubmul. These are genuine mathematical results and are preserved. The all-empty witness is only a satisfiability witness. Our finite product model and derived channels supply a positive-noise carrying example for coefficient21, not for35235.
* The hsubmul used there is μ(E∩F)≤μ(E)μ(F). Standard local-stochastic upper bounds μ(all S fail)≤p^{|S|} do not alone imply this stronger inequality between actual marginals. For example two identical events of probability p² satisfy the two-location rate-p joint bound and have each marginal≤p, yet p²>p^4. We preserve the source's actual conditional theorem and do not broaden its noise class from its prose. Our independent sibling construction supplies hsubmul exactly.
* Concatenation.lean defines an exact real recursion, DoubleExp.lean proves its conditional/general inequality, and AGP/Threshold.lean specializes the sequence to the stored count. All these true scalar consequences remain. A pure-pair inverse1/35235 is not AGP's full rigorous threshold. The current D6 text itself distinguishes corrected A'≈36108 and A''≈36511, cubic faults and ancilla acceptance, and the reported rigorous lower bound2.739×10^{-5}. No new numerical verification or primary-paper recheck occurred here.
* FaultTolerantUQC.lean packages density, ε≥0 and ε<steaneAGPThreshold. composition_substantive proves the conjunction of a density consequence and a real recursion consequence. Its sound SU-target migration is retained. It has no encoder, instrument, implemented noisy channel, per-word noise budget or derived simulation equality. Its qutrit examples are not silently qubit-Steane instantiations.
* GateCompilation.lean has an actual signed braid word, a30-crossing count, a matrix Hadamard target, an entrywise IsBHSZApprox predicate and density-hypothesis extraction. Its frobNormSq definition adds squares of entries without conjugation; that definition alone cannot certify a general complex Frobenius norm. Our norms in Sections2 and10 use absolute squares. RouabahSplitBraid.lean proves the literal take/drop/foldl factorization; this is useful actual syntax infrastructure and does not by itself supply the declared final approximation bound.
* CliffordTGeneratingSet.lean defines the actual phase-corrected h,t matrices and their free-group representation. CliffordTCompiler.lean's universally quantified source contract bounds approximation, recursion-level length and actual returned-word length at a constructive base finder. CompiledGateDiamond.lean explicitly converts its row-sum norm contract to a half-diamond bound with sqrt2. We have personally read these complete modules. This is stronger relevant source than an uninterpreted compiler predicate; no current native or transitive proof audit was run. We do not infer current kernel acceptance from headers. Section10's independent manual compiler uses no unexamined source theorem as a mathematical premise.
* RossSelinger/Compile.lean has an Option-returning bounded residual search and a soundness theorem with explicit residual/second-column approximation hypotheses. Its first-column scale lemma does not remove the second-column residual condition. The source's different synthesis routes, precision contracts and lengths must not be conflated.
* QuantumNetwork/FiniteInstrument.lean has actual finite normalized Kraus instruments, unnormalized/zero branches and arbitrary spectator lifts. UnitaryDiamond.lean has the explicit conjugation telescope and input-sized stabilized certificate. These source bodies support the semantic conventions; our proof still supplies its own finite matrices and all-reference reasoning.

The accepted B7 toric-code construction and its full independent review supplied a useful methodological pattern: define a Hilbert-space code, derive distance, complete every syndrome, build CPTP recovery and preserve references. That accepted [[2L²,2,L]] toric code does not prove the Steane claims in Sections3–6; those were derived independently from this source H. Neither code establishes horizon reconstruction, categorical equivalence or a topological hardware noise threshold.

## 15. Concrete remaining B5 construction, without reducing the objective

The original code→measurement→compiler→universal logic objective is retained in full, including its intended topological and fault-tolerant interpretation. The following distinctions are obligations of that objective, not invented completion gates for the bounded theorem above.

**Actual noisy error-correction gadgets.** Section13.5 gives a failed naive extraction attempt and the explicit propagation calculation. The next substantive construction is a verified ancilla/cat-state or verified encoded-Steane syndrome extractor: list its prep/CNOT/measurement locations; propagate each single fault through each stabilizer measurement; prove that a clean input plus one gadget fault leaves at most one data error and that a one-error input with a clean gadget is corrected; account for repeated/flagged syndrome decisions and ancilla acceptance. The residual is these concrete fault cases and their combination, not the already established code distance.

**Actual noisy universal gates.** Transversal Clifford identities were proved, but faults in their surrounding extraction circuits, ancilla preparation and feed-forward are absent from Section12. The T gadget has actual ideal branch matrices and an ideal magic resource; next derive noisy magic preparation/distillation and its acceptance/error map and combine it with the injection branches. An arbitrary-fidelity ideal |A_L> is not a physical fault-tolerance theorem. The repeated-T inverse and word counts provide a concrete target circuit for this analysis.

**Gadget fault sets and recursion.** With those concrete gadget circuits, define wrong-channel/decoded-output failure at each rectangle, establish good→correct with actual decoder boundaries, list malignant pairs or use a proved coarse all-pairs bound, include every higher fault set and acceptance conditioning, and derive a noise rate statement over actual physical locations. The source probability recursion can then be applied at its actual hypotheses. To recover the intended35,235/2.739×10^{-5} AGP statement, use the precise575-location AGP circuit/noise/acceptance convention; do not import its count into a different gadget. Overlapping extended rectangles require their own truncation/order or joint local-stochastic proof; disjoint-leaf independence from Section8 is insufficient. A coarse coefficient for a genuinely proved new gadget would be useful progress, even if different from AGP's.

**Intended physical gate carrier.** Match each actual braid/fusion gate's encoded computational subspace, leakage handling, dimension, order, phase and measurement map to H/T/CNOT or to a complete alternative universal alphabet. An SU(3) density statement on a qutrit does not automatically supply a binary Steane gate. Derive a per-word reference-stable error budget, including approximation and leakage, and incorporate its true length into (12.1). The target-channel telescope here is reusable after those carrier obligations are actually proved.

**Native and publication work.** The manual code, syndrome, Kraus and compiler constructions require native definitions and proofs with exact owning-source bindings; no import, build, Lean slot, test, compiler, numerical model or export was run. Full independent mathematical review has accepted the scoped ideal-control independent-storage operational theorem; fresh source review and native/physical validation remain separate. Existing closure/native/fullscience/physical/publication/main/human decisions remain with their owners; no readiness or bundle-green count is changed by this note.

This is the precise breakdown after the completed operational construction, not a claim of impossibility or an automatic deferral of B5. It identifies the next nontrivial gadgets and the concrete counterexample that prevents replacing their proof by distance alone.

## 16. Scope and provenance of this author artifact

Only this construction and its six companion ignored outputs were authorized writes. Project source, roadmaps, notebook, Git/index, holdings, models, runtime, native execution, compiler/build/render/export and external communication were not modified or invoked. The original first continuity check was fresh; the original final check records only owned-output creation. Input hashes and original command channels are supplied in evidence/process receipts. Hash equality establishes provenance, not mathematical acceptance. The original document and full nonauthor mathematical review remain frozen; this documentary copy requires fresh complete independent source-contract review.
