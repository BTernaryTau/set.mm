$[ set.mm $]

$( ADVENT OF METAMATH 2025!

   The task is to prove a variety of results about the provability logic GL (and a few results about a weaker logic K4).
   The results about GL can be interpreted in terms of provability in Peano arithmetic, in particular some famous statements
   about provability (like Godel's second theorem) can be expressed (and proved) in this logic.

   The proofs don't require anything besides theorems of propositional logic and the definitions and axioms from this file,
   so one can load set.mm only up to theorem ~ wex , and it should be sufficient for the proofs.
   No knowledge of Godel's theorems of proof theory are required, but theorem comments try to provide some context anyway.

   The proofs are usually fairly short (and sometimes trivial), so some statements are grouped into one day (for example, Day 1a and Day 1b).
   If you get stuck on some problem, one can usually find the solution in the book Boolos "The logic of provability", chapters 1 and 3.

   Have fun!
$)

$c []. $.

$( If ` ph ` is a wff, then ` []. ph ` is a wff.  The box symbol ` []. ` can
   be read as "necessarily", or "provable" in the case of the provability logic. $)
cbox $a wff []. ph $.

${
  ax-necess.1 $e |- ph $.
  $( The necessitation rule: if something is true, it is necessary true. $)
  ax-necess $a |- []. ph $.
$}

$( The distribution axiom.  This axiom together with ~ ax-necess defines the weakest normal modal logic K. $)
ax-distrb $a |- ( []. ( ph -> ps ) -> ( []. ph -> []. ps ) ) $.

${
  monrule.1 $e |- ( ph -> ps ) $.
  $( Day 1a.  The monotony rule. $)
  monrule $p |- ( []. ph -> []. ps ) $= ? $.
$}

${
  monbirule.1 $e |- ( ph <-> ps ) $.
  $( Day 1b.  The monotony rule for biimplications. $)
  monbirule $p |- ( []. ph <-> []. ps ) $= ? $.
$}

$( Day 2.  Box can be distributed through conjunction. $)
distrconj $p |- ( []. ( ph /\ ps ) <-> ( []. ph /\ []. ps ) ) $= ? $.

${
  monimpconj.1 $e |- ( ( ph /\ ps ) -> ch ) $.
  $( Day 3a.  Monotony for an implication with a conjunction inside. $)
  monimpconj $p |- ( ( []. ph /\ []. ps ) -> []. ch ) $= ? $.
$}

$( Day 3b.  Box can be "factored out" of a disjunction in one direction. $)
distrdisj $p |- ( ( []. ph \/ []. ps ) -> []. ( ph \/ ps ) ) $= ? $.

$c <>. $.

$( If ` ph ` is a wff, then ` <>. ph ` is a wff.  The diamond symbol ` <>. `
   can be read as "possibly" and it is defined in terms of ` []. ` .  In the
   case of provability logic, ` <>. ph ` can be interpreted as " ` ph ` is
   consistent with Peano arithmetic". $)
cdiam $a wff <>. ph $.

$( The definition of ` <>. ` in terms of ` []. ` .
   I.e. ` ph ` is consisent with Peano arithmetic if and only if
   it is not provable that ` ph ` is false. $)
df-diam $a |- ( <>. ph <-> -. []. -. ph ) $.

${
  monruled.1 $e |- ( ph -> ps ) $.
  $( Day 4a.  The monotony rule (for diamond). $)
  monruled $p |- ( <>. ph -> <>. ps ) $= ? $.
$}

${
  monbiruled.1 $e |- ( ph <-> ps ) $.
  $( Day 4b.  The monotony rule for biimplications (for diamond). $)
  monbiruled $p |- ( <>. ph <-> <>. ps ) $= ? $.
$}

$( Day 5.  Diamond can be distributed through conjunction in one
   direction. $)
distrconjd $p |- ( <>. ( ph /\ ps ) -> ( <>. ph /\ <>. ps ) ) $= ? $.

$( Day 6.  Diamond can be distributed through disjunction. $)
distrdisjd $p |- ( <>. ( ph \/ ps ) <-> ( <>. ph \/ <>. ps ) ) $= ? $.

$( Day 7.  If we have a conjunction of a diamond and a box, we can "factor" the diamond out. $)
dandb $p |- ( ( <>. ph /\ []. ps ) -> <>. ( ph /\ ps ) ) $= ? $.

$( The Godel-Lob axiom, which defines the logic GL. In this logic ` []. ` is
   interpreted as "provable in Peano arithmetic (PA)".  In particular, this
   axiom corresponds to Lob's theorem, which shows that if the statement
   ` []. ph -> ph ` is provable in PA, then ` ph ` is provable in PA. Since
   we are studying an abstract modal logic, we do not need to worry about PA,
   but of course all the results we'll obtain will have consequences for
   provability in PA. $)
ax-gl $a |- ( []. ( []. ph -> ph ) -> []. ph ) $.

$( Day 8a.  Modal logic K4 extends K with an axiom ` [] ph -> []. []. ph ` .
   Turns out this axiom is true in GL, hence GL extends K4.  One can
   interpret this result as: if something is provable, then it's provable
   that it's provable. $)
axk4 $p |- ( []. ph -> []. []. ph ) $= ? $.

$( Day 8b.  Another form of ~ axk4 . $)
axk4d $p |- ( <>. <>. ph -> <>. ph ) $= ? $.

${
  sdsdeqsdlem.1 $e |- []. ( ( ph /\ ps ) -> th ) $.
  $( Day 9a.  Two simple lemmata for ~ sdsdeqsd .  The proofs should reply
     on ~ axk4 and its corollaries, not on ~ ax-gl . $)
  sdsdeqsd1lem1 $p |- []. ( ( <>. ph /\ []. ps ) -> <>. th ) $= ? $.

  $( Day 9b. $)
  sdsdeqsd1lem2 $p |- []. ( ( []. ph /\ <>. ps ) -> <>. th ) $= ? $.
$}

$( Day 10.  Operator ` []. <>. ` applied twice equals itself in logic K4.
   This proof again shouldn't rely on ~ ax-gl directly. $)
sdsdeqsd $p |- ( []. <>. []. <>. ph <-> []. <>. ph ) $= ? $.

$( Day 11.  A certain argument in the proof of Lob's theorem.  Again, don't
   rely on ~ ax-gl directly. $)
lobstep $p |- ( []. ( ps <-> ( []. ps -> ph ) ) -> ( []. ( []. ph -> ph ) -> []. ph ) ) $= ? $.

$( Day 12a.  An unusual consequence of ~ ax-gl which works for any formulae
   ` ph ` and ` ps ` .  This could be interpreted as "if we can prove that
   ` ph ` is consistent with PA, then we can prove anything". From now on
   we can use ~ ax-gl in proofs again. $)
kurbis $p |- ( []. <>. ph -> []. ps ) $= ? $.

$( Day 12b.  We can prove False (i.e.  PA is inconsistent) if and only if we
   can prove consistency for any sentence ` ph ` . $)
bfbdp $p |- ( []. F. <-> []. <>. ph ) $= ? $.

$( Day 13.  Godel's second theorem can be proved in PA. Namely, if PA is
   consistent ( ` -. []. F. ` ), then we can't prove in PA that it's
   consistent. $)
godel2 $p |- ( -. []. F. -> -. []. -. []. F. ) $= ? $.

$( Day 14.  Note that ` []. ph \/ []. -. ph ` can be interpreted as " ` ph `
   is decidable".  Hence the following means that if inconsistency of PA is
   not provable, then the consistency of PA is undecidable. $)
incundec $p |- ( -. []. []. F. -> -. ( []. -. []. F. \/ []. -. -. []. F. ) ) $= ? $.

$( Day 15.  Lemma for ~ equiva . $)
equivalem $p |- ( []. ( ph <-> -. []. ph ) -> []. ( ph <-> -. []. F. ) ) $= ? $.
$( Day 16.  It is provable that a statement ` ph ` is equivalent to the
   assertion that ` ph ` is unprovable if and only if it is provable that
   ` ph ` is equivalent to PA being consistent. $)
equiva $p |- ( []. ( ph <-> -. []. ph ) <-> []. ( ph <-> -. []. F. ) ) $= ? $.
$( Day 17.  A corollary from ~ equiva .  It is provable that ` ph ` is
   equivalent to the assertion that ` ph ` is disprovable if and only if it
   is provable that ` ph ` is equivalent to PA being inconsistent. $)
equivacor $p |- ( []. ( ph <-> []. -. ph ) <-> []. ( ph <-> []. F. ) ) $= ? $.
$( Day 18.  It is probable that ` ph ` is equivalent to the assertion that
   ` ph ` is provable if and only if it is provable that ` ph ` is equivalent
   to anything that is provable. $)
equivb $p |- ( []. ( ph <-> []. ph ) <-> []. ( ph <-> T. ) ) $= ? $.
$( Day 19. It is provable that ` ph ` is equivalent to the assertion that
   ` ph ` is consistent with PA if and only if it is provable that ` ph ` is
   equivalent to anything that is disprovable. $)
equivbcor $p |- ( []. ( ph <-> <>. ph ) <-> []. ( ph <-> F. ) ) $= ? $.

$( Day 20.  Formula ` []. ph -> ph ` is called the reflection principle for
   ` ph ` , in particular, ~ ax-gl means that ` ph ` is provable if the
   reflection principle for ` ph ` is provable.  The following result means
   that there's no single reflection principle which implies
   ` -. []. []. F. ` .  See Boolos p. 63 for more context. $)
norefl $p |- ( []. ( ( []. ph -> ph ) -> -. []. []. F. ) -> []. []. F. ) $= ? $.

$c [.] $.

$( If ` ph ` is a wff, then ` [.] ph ` is a wff. $)
cdbox $a wff [.] ph $.

$( The definition of the "dotted box" ` [.] ` in terms of ` []. ` .  This
   definition makes sense, since ` []. ph -> ph ` is not, in general, a
   theorem of GL. $)
df-dbox $a |- ( [.] ph <-> ( []. ph /\ ph ) ) $.

$( The following five results prove some properties of the dotted box. One can use ~ axk4 but not ~ ax-gl in the proofs. $)
$( Day 21. $)
dbbeqb $p |- ( [.] []. ph <-> []. ph ) $= ? $.
$( Day 22. $)
dbbeqbdb $p |- ( [.] []. ph <-> []. [.] ph ) $= ? $.
$( Day 23. $)
dbeqdbdb $p |- ( [.] ph <-> [.] [.] ph ) $= ? $.

${
  dbimp.1 $e |- ( [.] ph -> ps ) $.
  $( Day 24a. $)
  dbimp1 $p |- ( []. ph -> []. ps ) $= ? $.
  $( Day 24b. $)
  dbimp2 $p |- ( [.] ph -> [.] ps ) $= ? $.
$}

$( Day 25a.  Lemma for ~ puzzle . $)
puzzlelem $p |- ( [.] ( [.] ( ph -> [.] ph ) -> ph ) -> []. ( ph -> [.] ph ) ) $= ? $.

$( Day 25b.  A puzzle from Boolos' book, see p. 164 for a solution. $)
puzzle $p |- ( [.] ( [.] ( ph -> [.] ph ) -> ph ) -> ph ) $= ? $.