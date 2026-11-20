# Focused original Eq7 MAIN source-composition review R1

**REVISE_IMPORT_PLACEMENT**, candidate `da589c0cd11df218361e1175ea8c83b9ddcccaea`. First same-packet check is fresh=true, changed=[]. ROOT paused acceptance and will deliberately reissue R2 after correction; terminal snapshot status is retained in JSON.

The entire diff is exactly nine new accepted modules and nine aggregate import lines relative to actual main `ce194cdc4bf939b108c17edc9530a7f0a14565f9`. All nine modules match accepted primary `056ccb9f08454238934977de4bb6548d18c6275e` byte-for-byte. All recursively reached pre-existing project modules and toolchain/lakefile.toml/manifest match actual main. No unrelated paper, constants, frontier or primary-only NavierStokes configuration entered. Complete diff, all module sources/hashes and exact dependency/configuration comparisons are retained in JSON.

Required repair: `lean/SKEFTHawking.lean:5276` appends imports after the existing module-documentation command instead of placing them in the leading import header. The aggregate is byte-exact old main followed by those nine lines, so preservation alone does not establish valid import command ordering. Move ONLY those lines into the header, commit, and obtain independent fresh R2 composition review. ROOT reported its standalone native R1 caught this invalid import; reviewer ran no build or Lean command. This is aggregate integration error, not a mathematical theorem/source defect.

An initial read-only conservation script guessed lakefile.lean and failed; actual canonical config is lakefile.toml, verified through rg --files and complete corrected conservation. This reviewer mistake is preserved in JSON and caused no source mutation.

Original individual source/kernel acceptances remain applicable subject to correct composition. No native, canonical, full merge or publication acceptance is granted. Existing full-project failures and physical Eq9–11/Haar/nonzeroZ/B2/B3 remain owed. No source/Git/runtime/build/cache/controller/notebook mutation performed.
