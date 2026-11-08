# Original N16 complete source and runtime review R1

The exact complete scalar candidate is a two-path patch on source
`34d14897cffb1fc23541c616eafb3f784c833e93`. Its installed diff SHA256 is
`8e5f7a4d51728aceec14a65d486bc8a96fb7999316d202d7cf5859b016f6f308`.
Both independent reviews matched their continuity inputs before and after.

The scientific review accepts the original scalar construction and its
complete test assertions. Bounded checks reproduce all 256 curvature
covariances, both-anchor temporal projection and both signed mixed
contractions in each convention. Without spectators the correct raw
core is `3645/2`. Dropping one chirality gives `3645/4`, dropping
the negative area term gives `3240`, and dropping the factorial gives
`7290`. The prior wrong-endpoint and missing-anchor controls remain.
The exact scientific selector collects one test. No full scientific
calculation ran.

Runtime admission is held. A one-byte valid budget reaches geometry
before reserving it. The measured 69,168 bytes of retained geometry and
direct result are absent from subsequent auxiliary reservation calls.
The mocked R1 launcher admitted two concurrent invocations and could
report success without checking normal-exit group quiescence or a
positive observation. Both defects are independently reproduced.
The source revision will pre-reserve geometry and charge retained state
through each allocator. The launcher revision is under separate
independent review and no launch token is issued.

[Exact author, scientific and adverse runtime evidence](ORIGINAL_TASK3_N16_COMPLETE_REVIEW_EVIDENCE_R1.zip)
contains 13 verified members, 21,975 bytes, SHA256
`5ecba26fb1201548adc764d5767eba13124b8644de910b5a870a0e75541c4789`.
Complete runtime, actual results, independent result review, formal
correspondence, full Z, physical B3 and publication acceptance remain
open. The parallel Task4 assignment addresses only the first exact
split-factor support certificate and does not evaluate full Z.
