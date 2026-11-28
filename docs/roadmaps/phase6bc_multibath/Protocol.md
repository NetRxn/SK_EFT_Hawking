# Frozen multibath schedule and calibration replay

Use actual diagonal Gibbs reset channels in the three-level case,
with targets A=(1/2,1/4,1/4), B=(1/4,1/2,1/4), C=(1/4,1/4,1/2).
Two finite interior targets are frozen. At equal doses log(2) use
the equal mixture of chronological block orders ABC, BCA and CAB.
At held-out doses (log(2),log(3),log(5)) use chronological block orders
ACB, BAC and CBA with mixing weights 1/4, 1/3 and 5/12, respectively.
Build one deterministic finite schedule for each from the common-cell
sliding-window construction. Verify the weight vector against the
independently accumulated mixed block weights, preserve every bath
dose and respect the proven maximum slice count. Check all subset
inequalities and exact total attenuation as appropriate.

For each interior case compare actual chronological affine operations
to the stated closed action on four inputs. Use a maximally mixed
system with a product spectator, a Bell-like input (|0,0>+|1,1>)/sqrt(2),
a nonmaximally entangled state sqrt(2/3)|0,1>+sqrt(1/3)|2,0>, and
one arbitrary trace-zero complex matrix with nonzero spectator
partial trace. Include identity on the spectator in every slice.
Use absolute tolerance 10^-10. No physical implementation is implied.

At equal doses compare the two chronological block orders BCA and
CBA as the named one-readout ambiguity control, using a maximally
mixed system for scalar calibration. Check the equal A detector,
distinct B detector and exact 1/32 output trace distance, with both
product and correlated inputs. Recover all coefficients from two
readouts and the known weight sum.

Run the exact two-bath minimax comparison for the fixed datum 11/16
and uncertainty 1/16. Report the reachable interval, inferred and
midpoint weights, the extremal compatible errors, and per-datum
diameter and global minimax radius. Replay the midpoint by a
finite chronological three-slice schedule. Keep the analytic claims
and finite floating-point tolerance checks distinct.
