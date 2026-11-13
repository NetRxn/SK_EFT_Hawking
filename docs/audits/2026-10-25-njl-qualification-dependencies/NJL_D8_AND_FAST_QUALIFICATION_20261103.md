# NJL fast qualification and D8 integration

The configured fast suite on frozen `48ed5d20` completed with 7,229 passes, 11 failures, nine skips and 92 deselections. Test-only loopback and process permissions and a temporary uv cache were available. The protected untracked stub digest matched before and after. The tracked checkout was clean at terminal readback.

Eleven failures group into three D1 hierarchy/floor reader tests, six module-reach and open-finding tests, and two count-literal ratchet tests. The D1 scalar migration had verified numeric and PDF parity, but did not cover all existing readers of the manuscript. That compatibility gap must be investigated before qualification. The current composition needs another exact failure readback.

Integration commit `62886aba` is a normal merge of the frozen base and the reviewed D8 package `fa8d5d79`, with identical tree to the reviewed package. The six new D8 closures 1.1, 1.2, 1.3, 1.5, 1.6 and 1.9 all read fixed. The candidate passed 13 focused figure, inventory, numerical-literal and apex ratchet tests. Module reach improved from 181 to 175 against 147, with D8 going from 33 to 27. D8 has 15 open findings, including one major. The portfolio unattributed count is 52 against 44, and per-bundle excesses remain. The original D8 1.7 remains open. No readiness promotion or main merge follows from this integration.
