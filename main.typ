#import "template.typ": *
#import "@preview/in-dexter:0.7.0": *

#show: project.with(
  title: "様相論理についての様々なメモ",
  authors: ("SnO2WMaN",),
  meta: json("meta.json"),
)

#let indexAxiom(display: $$, name: "") = index(
  initial: (letter: "こ"),
  index: "Axiom",
  display: display,
  "公理!" + name,
)
#let indexLogic(display: $$, name: "") = index(
  initial: (letter: "よ"),
  index: "Logic",
  display: display,
  "様相論理!" + name,
)

= はじめに．

この文書は標準的な様相論理の様々な体系についてのメモである．


= 公理 $AxiomM$ とMcKinsey的関係

まず定義を述べていく．

#definition[様相論理の公理 $AxiomM$][
  以下を様相論理の公理 $AxiomM$ #indexAxiom(display: $AxiomM$, name: "M") と言う．
  $
    AxiomM equiv box dia p -> dia box p
  $
]


#definition[McKinsey的関係][
  2項関係 $R$ が以下を満たすなら，$R$ はMcKinsey的関係#index[McKinsey的関係]であるという．
  $
    forall x. exists y. [x R y and forall z.[y R z -> y = z]]
  $
]

#remark[
  Kripkeフレームの言葉で言えば，$R$ がMcKinsey的であるなら，全ての点が終点としてsimpleなクラスターに辿り着くことが保証される．
]

#let LogicKM = Logic("KM")
#let LogicK4M = Logic("K4M")
#let LogicS4M = Logic("S4M")
#let LogicK4 = Logic("K4")

#let oplus = $plus.circle$

== $LogicK4M, LogicS4M$ について

公理 $AxiomM$ を含む体系のうち，$LogicK4M, LogicS4M$ は比較的行儀の良い体系である．

#definition[様相論理 $LogicK4M, LogicS4M$][
  - $LogicK4M = LogicK4 oplus AxiomM$ #indexLogic(display: $LogicK4M$, name: "K4M")
  - $LogicS4M = LogicS4 oplus AxiomM$ #indexLogic(display: $LogicS4M$, name: "S4M")
]
#remark[
  C&Z では $LogicK4M$ は $Logic("K4.1")$，$LogicS4M$ は $Logic("S4.1")$ となっている．
  しかし歴史的経緯で違う公理を足したものを $Logic("S4.1")$ と呼ぶ文献 @hughesNewIntroductionModal2007 もあり紛らわしいため，
  このメモでは $LogicK4M, LogicS4M$ と呼ぶことにする．
]

#definition[
  // - Mckinsey的関係のフレームクラスを $C_LogicKM$ と書く．
  - 推移的かつMckinsey的関係のフレームクラスを $C_LogicK4M$ と書く．
  - 前順序かつMckinsey的関係のフレームクラスを $C_LogicS4M$ と書く．
]

まずはKripke意味論に対する健全性および無矛盾性を証明しよう．

#lemma[
  $F$ がMckinsey的なら，$F vDash AxiomM$．
] <lem:validate_axiomM_of_mckinseyan>
#proof[
  対偶を証明する．すなわち，$F nvDash AxiomM$ ならば $F$ はMckinsey的ではないことを証明する．

  証明は2パートに分ける．
  まず，$F nvDash AxiomM$ ならば $F$ は次を満たすことを示す．
  $
    exists x. forall y. [x R y -> exists u, v.[y R u and y R v and u != v]]
  $
  #struct[
    仮定より，ある $forces, x in F$ があって，$angle.l F, forces angle.r, x nvDash box dia p -> dia box p$ となる．
    今この $x$ が所望の $x$ であることを示す．任意に $x R y$ となる $y$ を取る．
    $y R u, y R v$ かつ $u != v$ となる $u, v$ が存在することを示せばよい．

    定義より次が成り立つ．
    $
      angle.l F, forces angle.r, x &vDash box dia p #<lem:validate_axiomM_of_mckinseyan:eq:1> \
      angle.l F, forces angle.r, x &nvDash dia box p #<lem:validate_axiomM_of_mckinseyan:eq:2>
    $

    @lem:validate_axiomM_of_mckinseyan:eq:1 より，
    $angle.l F, forces angle.r, y vDash dia p$ が言えて，ここから $angle.l F, forces angle.r, u vDash p$ となる $u$ の存在を言える．

    他方 @lem:validate_axiomM_of_mckinseyan:eq:2 より，
    任意の $x R z$ となる $x'$ で $angle.l F, forces angle.r, x' nvDash box p$ である．
    $x'$ として $y$ とすれば，$y R v$ かつ $v nvDash p$ となる $v$ の存在が言える．

    このとき，$u != v$ であることはありえない：仮に $u = v$ とすると，$u vDash p$ かつ $u nvDash p$ となりおかしい．

    以上より，$y R u, y R v$ かつ $u != v$ となる $u, v$ の存在を示せた．
  ]

  次に，この性質がMckinsey的関係の否定を導くことを示す．
  $
    exists x. forall y. [x R y -> exists z.[y R z and y != z]]
  $

  #struct[
    まず，$x$ を取ってきて，これが所望の $x$ であることを示す．
    任意の $x R y$ となる $y$ を取る．
    $x$ の仮定より，$u,v$ が取れて，$y R u$ かつ $y R v$ かつ $u != v$．
    $y = u$ か否かで場合分けする．
    $y = u$ であるなら $z$ として $v$ とすればよく，
    $y != u$ であるなら $z$ として $u$ とすればよい．
  ]
]

一方，@lem:validate_axiomM_of_mckinseyan の逆方向は $F$ が推移的であることを仮定しなければならない．
これにより，推移性が保証される $LogicK4M, LogicS4M$ についてのみ考えることになる．

#lemma[
  推移的な $F$ で $F vDash AxiomM$ なら，$F$ はMcKinsey的である．
]
#proof[
  // TODO:
]

以上より次の @cor:mckinsey_frameclasses_definability が成り立つ．

#corollary[
  // - $AxiomM$ は Mckinsey的な関係のフレームクラスを規定する．
  - ${Axiom4, AxiomM}$ は $C_LogicK4M$ を規定する．
  - ${AxiomT, Axiom4, AxiomM}$ は $C_LogicS4M$ を規定する．
] <cor:mckinsey_frameclasses_definability>

体系の無矛盾性を示すにはフレームクラスの非空性を言えばよかった．

#lemma[
  $C_LogicK4M, C_LogicS4M$ は空でない．
] <lem:mckinsey_frameclasses_nonempty>
#proof[
  両方のケースで，反射的な単点フレームが条件を満たす．
]

#corollary[$LogicK4M, LogicS4M$ のKripke健全性および無矛盾性][
  $LogicK4M, LogicS4M$ はそれぞれ $C_LogicK4M, C_LogicS4M$ に対して健全でありかつ無矛盾である．
]
#proof[
  @cor:mckinsey_frameclasses_definability と @lem:mckinsey_frameclasses_nonempty より従う．
]


次にKripke意味論に対する完全性を証明する．$LogicK4M, LogicS4M$ はそれぞれカノニカルであり，それから完全性が従う．

#theorem[
  $LogicK4M, LogicS4M$ はそれぞれカノニカルである．
]

#proof[

]

#theorem[$LogicK4M, LogicS4M$ のKripke完全性][
  $LogicK4M, LogicS4M$ はそれぞれ $C_LogicK4M, C_LogicS4M$ に対して完全である．
]

== $LogicKM$ について

#definition[様相論理 $LogicKM$][
  $LogicKM = LogicK oplus AxiomM$ #indexLogic(display: $LogicKM$, name: "KM")
]

$LogicKM$ に関しては次のことが成り立つらしいが，証明は不明．

#proposition[C&Z p.138][
  $LogicKM$ はカノニカルではない．
]

#proposition[@hughesNewIntroductionModal2007[p.367]][
  $LogicKM subset LogicS4M$
]


#heading(numbering: none)[索引]

#columns(3)[
  #make-index(
    use-bang-grouping: true,
    use-page-counter: true,
    sort-order: upper,
    range-delimiter: [--],
  )
]

