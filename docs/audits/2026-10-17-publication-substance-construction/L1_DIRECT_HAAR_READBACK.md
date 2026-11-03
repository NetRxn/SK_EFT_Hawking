# L1 direct Haar contraction readback

The independent exact runs reproduced the two-site contributions A = 2922 and mixed = 0. The direct quaternion expansion integrates the actual plaquette vector norms. It gives marginal moments 3/4 and correlated moment 41/72, with 96,217 monomials and 7,536 all-even terms. Sharing the conjugating link between the two plaquettes changes the correlated moment to 7/12. The distinct-direction factorization uses independent transverse links.

The local contraction reconstructs the axial bilinears using the existing wedge engine. Six antisymmetric basis values equal 3, and all fifteen basis-pair sums equal 6. Omitting one orientation changes the selected value to 13/8. The exact center-parity enumeration kills all 81 mixed terms and leaves nine terms each for A and B. The direct SU(2) commutator covariance is (2/9) times the identity and verifies the curvature input to B.

The independent adversarial reviewer reran all three checks and accepted the scoped contractions. The rest of B still uses the reduced reference. The unpruned full contraction, physical tensor matching, and susceptibility window remain open. Mutation controls are in-memory comparisons.

Run these files with the repository Python environment:

- [Direct quaternion moments](l1_direct_a_haar.py)
- [Local wedge contractions](l1_direct_local_a_wedge.py)
- [Center parity and commutator covariance](l1_direct_haar_parity.py)
