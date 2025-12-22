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
  monrule $p |- ( []. ph -> []. ps ) $= ( wi cbox ax-necess ax-distrb ax-mp ) ABDZEAEBEDICFABGH $.
$}

${
  monbirule.1 $e |- ( ph <-> ps ) $.
  $( Day 1b.  The monotony rule for biimplications. $)
  monbirule $p |- ( []. ph <-> []. ps ) $= ( cbox biimpi monrule biimpri impbii ) ADBDABABCEFBAABCGFH $.
$}

$( Day 2.  Box can be distributed through conjunction. $)
distrconj $p |- ( []. ( ph /\ ps ) <-> ( []. ph /\ []. ps ) ) $= ( wa cbox simpl monrule simpr jca wi pm3.2 ax-distrb syl imp impbii ) ABCZDZADZBDZCPQROAABEFOBABGFHQRPQBOIZDRPIASABJFBOKLMN $.

${
  monimpconj.1 $e |- ( ( ph /\ ps ) -> ch ) $.
  $( Day 3a.  Monotony for an implication with a conjunction inside. $)
  monimpconj $p |- ( ( []. ph /\ []. ps ) -> []. ch ) $= ( cbox wa distrconj monrule sylbir ) AEBEFABFZECEABGJCDHI $.
$}

$( Day 3b.  Box can be "factored out" of a disjunction in one direction. $)
distrdisj $p |- ( ( []. ph \/ []. ps ) -> []. ( ph \/ ps ) ) $= ( cbox wo orc monrule olc jaoi ) ACABDZCBCAIABEFBIBAGFH $.

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
  monruled $p |- ( <>. ph -> <>. ps ) $= ( wn cbox cdiam con3i monrule df-diam 3imtr4i ) ADZEZDBDZEZDAFBFNLMKABCGHGAIBIJ $.
$}

${
  monbiruled.1 $e |- ( ph <-> ps ) $.
  $( Day 4b.  The monotony rule for biimplications (for diamond). $)
  monbiruled $p |- ( <>. ph <-> <>. ps ) $= ( cdiam biimpi monruled biimpri impbii ) ADBDABABCEFBAABCGFH $.
$}

$( Day 5.  Diamond can be distributed through conjunction in one
   direction. $)
distrconjd $p |- ( <>. ( ph /\ ps ) -> ( <>. ph /\ <>. ps ) ) $= ( wa cdiam simpl monruled simpr jca ) ABCZDADBDIAABEFIBABGFH $.

$( Day 6.  Diamond can be distributed through disjunction. $)
distrdisjd $p |- ( <>. ( ph \/ ps ) <-> ( <>. ph \/ <>. ps ) ) $= ( wn cbox wa wo cdiam ianor df-diam distrconj notbii ioran monbirule xchnxbir bitri orbi12i 3bitr4i ) ACZDZBCZDZEZCZSCZUACZFABFZGZAGZBGZFSUAHUGUFCZDZCUCUFIRTEZDZUCUKUMUBRTJKUJULABLMNOUHUDUIUEAIBIPQ $.

$( Day 7.  If we have a conjunction of a diamond and a box, we can "factor" the diamond out. $)
dandb $p |- ( ( <>. ph /\ []. ps ) -> <>. ( ph /\ ps ) ) $= ( cdiam cbox wa wn wi df-diam imnan biimpri con2d monrule ax-distrb syl com12 con3rr3 sylbi imbitrrdi imp ) ACZBDZABEZCZTUAUBFZDZFZUCTAFZDZFUAUFGAHUAUEUHUEUAUHUEBUGGZDUAUHGUDUIUDABABFGUDABIJKLBUGMNOPQUBHRS $.

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
axk4 $p |- ( []. ph -> []. []. ph ) $= ( cbox wa wi distrconj idd adantrd anc2li biimtrid monrule ax-gl simprbi 3syl ) ABZANCZBZODZBPNBZAQPNRCZAOANEZASNANNRANFGHIJOKPNRTLM $.

$( Day 8b.  Another form of ~ axk4 . $)
axk4d $p |- ( <>. <>. ph -> <>. ph ) $= ( wn cbox cdiam axk4 con3i df-diam bicomi con1bii monbirule notbii bitr2i 3imtr3i ) ABZCZCZBZOBZADZDZSOPNEFTSBZCZBQSGUBPUAOOSSRAGHZIJKLUCM $.

${
  sdsdeqsdlem.1 $e |- []. ( ( ph /\ ps ) -> th ) $.
  $( Day 9a.  Two simple lemmata for ~ sdsdeqsd .  The proofs should rely
     on ~ axk4 and its corollaries, not on ~ ax-gl . $)
  sdsdeqsd1lem1 $p |- []. ( ( <>. ph /\ []. ps ) -> <>. th ) $= ( cdiam cbox wa wi dandb wn con3 monrule ax-distrb mp2b con3i df-diam 3imtr4i syl ax-necess ) AEBFGZCEZHTABGZEZUAABIUBJZFZJCJZFZJUCUAUGUEUBCHZFUFUDHZFUGUEHDUHUIUBCKLUFUDMNOUBPCPQRS $.

  $( Day 9b. $)
  sdsdeqsd1lem2 $p |- []. ( ( []. ph /\ <>. ps ) -> <>. th ) $= ( cdiam cbox wa wi ancomst monbirule mpbi sdsdeqsd1lem1 ) BEZAFZGCEZHZFNMGOHZFBACABGCHZFBAGCHZFDRSABCIJKLPQMNOIJK $.
$}

$( Day 10.  Operator ` []. <>. ` applied twice equals itself in logic K4.
   This proof again shouldn't rely on ~ ax-gl directly. $)
sdsdeqsd $p |- ( []. <>. []. <>. ph <-> []. <>. ph ) $= ( cdiam cbox wa axk4 ancli distrconj sylibr wi simpr ax-necess sdsdeqsd1lem1 sdsdeqsd1lem2 ax-distrb ax-mp axk4d 3syl monrule dandb distrconjd sylan2 syl impbii ) ABZCZBZCZUEUGUFUGDZCZUDBZBZBZCZUEUGUGUGCZDUIUGUNUFEFUFUGGHUHULICUIUMIUEUFUKUDUEUJAUDUDAUDDUDIAUDJKLMLUHULNOULUDULUKUJUDUJPUDPAPQRQUEUDUEDZCZUGUEUEUECZDUPUEUQUDEZFUDUEGHUOUFUEUDUQUFURUDUQDAUEDBUDUFDUFAUESAUETUDUFJQUARUBUC $.

$( Day 11.  A certain argument in the proof of Lob's theorem.  Again, don't
   rely on ~ ax-gl directly. $)
lobstep $p |- ( []. ( ps <-> ( []. ps -> ph ) ) -> ( []. ( []. ph -> ph ) -> []. ph ) ) $= ( cbox wi wb axk4 biimp monrule ax-distrb syl5 imim2i pm2.43d 3syl syl imim2 biimpr sylcom com12 ) ACZADZCZBBCZADZEZCZSUAUEUBSUAUEUCCZUBUEUBSDZCZUAUFUEUECUHUDFUEUGUEBUCDZCUBUFDZUGUDUIBUCGHBUCIUJUBSUFUGUBUBUBCUFSBFUBAIJKLMZHNUAUGUCDZCUHUFDTULSAUBOHUGUCINJUEUCBDZCUFUBDUDUMBUCPHUCBINQUKQR $.

$( Day 12a.  An unusual consequence of ~ ax-gl which works for any formulae
   ` ph ` and ` ps ` .  This could be interpreted as "if we can prove that
   ` ph ` is consistent with PA, then we can prove anything". From now on
   we can use ~ ax-gl in proofs again. $)
kurbis $p |- ( []. <>. ph -> []. ps ) $= ( cdiam cbox wtru wfal trud monruled monrule wi wn df-diam df-fal monbirule notbii bitr4i pm2.21 sylbi ax-gl syl falim 3syl ) ACZDEZCZDZFZDZBDUCUEAUDAGHIUFUHUGJZDUHUEUIUEUHKZUIUEUDKZDZKUJUDLUHULUGUKMNOPUHUGQRIUGSTUGBBUAIUB $.

$( Day 12b.  We can prove False (i.e.  PA is inconsistent) if and only if we
   can prove consistency for any sentence ` ph ` . $)
bfbdp $p |- ( []. F. <-> []. <>. ph ) $= ( wfal cbox cdiam falim monrule kurbis impbii ) BZCADZCIJJEFAIGH $.

$( Day 13.  Godel's second theorem can be proved in PA. Namely, if PA is
   consistent ( ` -. []. F. ` ), then we can't prove in PA that it's
   consistent. $)
godel2 $p |- ( -. []. F. -> -. []. -. []. F. ) $= ( wfal cbox wn wtru cdiam kurbis con3i df-fal monbirule notbii df-diam bitr4i sylnibr ) AZBZCZDZEZBZPBSOQNFGPRPQCZBZCROUANTHIJQKLIM $.

$( Day 14.  Note that ` []. ph \/ []. -. ph ` can be interpreted as " ` ph `
   is decidable".  Hence the following means that if inconsistency of PA is
   not provable, then the consistency of PA is undecidable. $)
incundec $p |- ( -. []. []. F. -> -. ( []. -. []. F. \/ []. -. -. []. F. ) ) $= ( wfal cbox wn wo wtru cdiam df-diam df-fal monbirule notbii bitr4i kurbis sylbir notnotr monrule jaoi con3i ) AZBZCZBZTCZBZDSBZUAUDUCUAEZFZBUDUFTUFUECZBZCTUEGSUHRUGHIJKIUESLMUBSSNOPQ $.

$( Day 15.  Lemma for ~ equiva . $)
equivalem $p |- ( []. ( ph <-> -. []. ph ) -> []. ( ph <-> -. []. F. ) ) $= ( cbox wn wb wfal axk4 wi biimp monrule ax-distrb syl biimpr impbid cdiam bfbdp notnotb monbirule notbii df-diam bitr4i bitr4di notbid bitr monimpconj mpdan ) AABZCZDZBZUGEBZCZDZBZAUKDZBUIUIBUMUHFUIULUIUFUJUIUFUGBZUJUIUFUOUIAUGGZBUFUOGUHUPAUGHIAUGJKUIUGAGZBUOUFGUHUQAUGLIUGAJKMUJACZNZBUOUROUGUSUGURCZBZCUSUFVAAUTAPQRURSTQTUAUBIKUHULUNAUGUKUCUDUE $.

$( Day 16.  It is provable that a statement ` ph ` is equivalent to the
   assertion that ` ph ` is unprovable if and only if it is provable that
   ` ph ` is equivalent to PA being consistent. $)
equiva $p |- ( []. ( ph <-> -. []. ph ) <-> []. ( ph <-> -. []. F. ) ) $= ( cbox wn wb wfal equivalem wi axk4 wa simpl a1i biimp impcom monrule ax-distrb syl godel2 nsyli syl5 pm5.1im syl6c expd con1 biimpr syl11 imp falim 2thd con2bid ex pm2.61d1 mpcom impbii ) AABZCZDZBZAEZBZCZDZBZAFVAUPGZBZVBUQVBVBBVDVAHVBVCVBAVCVBAVAUPVBAVAIZAUOUPVEAGVBAVAJKVEUTVBUOVAAUTAUTLZMVBUNUTBZUTVBAUTGZBUNVGGVAVHVFNAUTOPQRSAUOTUAUBACZVAUPVIVAIZUNAVJUNVIVJUSUNVIVAUSUTAGVIUSVAUSAUCAUTUDUEUFURAAUGNPVIVAJUHUIUJUKNPVAUPOULUM $.

$( Day 17.  A corollary from ~ equiva .  It is provable that ` ph ` is
   equivalent to the assertion that ` ph ` is disprovable if and only if it
   is provable that ` ph ` is equivalent to PA being inconsistent. $)
equivacor $p |- ( []. ( ph <-> []. -. ph ) <-> []. ( ph <-> []. F. ) ) $= ( wn cbox wb wfal equiva notbi monbirule 3bitr4i ) ABZJCZBDZCJECZBDZCAKDZCAMDZCJFOLAKGHPNAMGHI $.

$( Day 18.  It is probable that ` ph ` is equivalent to the assertion that
   ` ph ` is provable if and only if it is provable that ` ph ` is equivalent
   to anything that is provable. $)
equivb $p |- ( []. ( ph <-> []. ph ) <-> []. ( ph <-> T. ) ) $= ( cbox wb wtru wi biimpr monrule ax-gl syl tbtru monbirule sylib axk4 ax-1 wa dfbi2 biimpri monimpconj syl2anc sylbir impbii ) AABZCZBZADCZBZUDUBUFUDUBAEZBZUBUCUGAUBFGAHIAUEAJKZLUFUBUDUIUBAUBEZBZUHUDUBUBBUKAMUBUJUBANGIAUGAUBNGUJUGUCUCUJUGOAUBPQRSTUA $.

$( Day 19. It is provable that ` ph ` is equivalent to the assertion that
   ` ph ` is consistent with PA if and only if it is provable that ` ph ` is
   equivalent to anything that is disprovable. $)
equivbcor $p |- ( []. ( ph <-> <>. ph ) <-> []. ( ph <-> F. ) ) $= ( wn cbox wb wtru cdiam wfal equivb df-diam bibi2i con2bi bicom 3bitri monbirule nbfal tbtru bitr3i 3bitr4i ) ABZSCZDZCSEDZCAAFZDZCAGDZCSHUDUAUDATBZDTSDUAUCUFAAIJATKTSLMNUEUBUESUBAOSPQNR $.

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
dbbeqb $p |- ( [.] []. ph <-> []. ph ) $= ( cbox cdbox wa df-dbox simpr axk4 ancri impbii bitri ) ABZCKBZKDZKKEMKLKFKLAGHIJ $.
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