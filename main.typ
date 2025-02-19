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

= はじめに

この文書は標準的な様相論理の様々な体系についてのメモである．
基本的に証明などは書き途中であり，またそもそも命題の正しさについても保証はしない．
誤りなどがあったらGitHubのIssueなどで指摘していただけると助かる．

= 公理 $AxiomM$ とMcKinsey的関係

まず定義を述べていく．

#definition[様相論理の公理 $AxiomM$][
  以下を様相論理の公理 $AxiomM$ #indexAxiom(display: $AxiomM$, name: "M") と言う．
  $
    AxiomM equiv box dia p -> dia box p
  $
]


#definition[McKinsey的関係][
  2項関係 $R$ が以下を満たすなら，$R$ は*McKinsey的*#index[McKinsey的]であるという．
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

= 非稠密拡大

非稠密拡大について述べる前に，まず，Post完全性の定義を確認しよう．

#definition[Post完全性][
  論理 $L$ が Post完全 #index([Post完全]) であるとは，論理 $L$ の無矛盾な真の拡大論理が存在しないことを言う．
]

#fact[
  古典命題論理 $Logic("Cl")$ はPost完全である．
]

#fact[
  直観主義命題論理 $Logic("Int")$ のPost完全な拡大論理は $Logic("Cl")$ のみである．
]

この定義を適当に相対化して，次のような定義#footnote[この名称はこの文書独自のもので，他に何というのかは知らない．]を考える．

#definition[正規様相論理の非稠密拡大][
  $L_0, L_1$ は正規様相論理であり $L_0 subset L_1$ とする．
  $L_1$ が $L_0$ の*正規様相論理の非稠密拡大*#index(initial: (letter: "せ"))[正規様相論理の非稠密拡大]であるとは，$L_0 subset L subset L_1$ となる真に中間かつ無矛盾な正規様相論理 $L$ が存在しないことを言う．
  以下，正規様相論理であることを考えていることが明らかな場合は単に非稠密拡大と呼ぶ．
]

#remark[
  拡大された $L_1$ が無矛盾であるかはどうでもよいことに注意せよ．
]

次のことはよく知られている．

#let LogicAll = $Logic("Fml")$
#let LogicKTc = $Logic("KTc")$

#proposition[
  $LogicAll$ は $LogicTriv, LogicVer$ の非稠密拡大である．
]

#proposition[
  $LogicTriv$ および $LogicVer$ は $LogicKTc$ の非稠密拡大である．
]

その他の例として，$LogicS5$ が非稠密拡大となる $LogicS4$ の拡大論理がある．

#let LogicS4Dot4 = $Logic("S4.4")$
#let LogicS4Dot9 = $Logic("S4.9")$
#let AxiomR1 = $Axiom("R1")$
#let AxiomM18 = $Axiom("M18")$

#definition[
  - $AxiomR1 equiv p -> (dia box p -> box p)$ #indexAxiom(display: $AxiomR1$, name: "R1")
  - $AxiomM18 equiv (dia box p -> p) or (box dia q -> dia box q)$ #indexAxiom(display: $AxiomM18$, name: "M18")
]

#definition[
  - $LogicS4Dot4 = LogicS4 oplus AxiomR1$ #indexLogic(display: $LogicS4Dot4$, name: "S4.4")
  - $LogicS4Dot9 = LogicS4Dot4 oplus AxiomM18$ #indexLogic(display: $LogicS4Dot9$, name: "S4.9")
]

#proposition[@hughesNewIntroductionModal2007[pp.284-287], Zeman 1973, pp.273-275][
  $LogicS5$ は $LogicS4Dot9$ の非稠密拡大である．
]

= 合流性および連結性について

合流性および連結性を規定する様相論理についていくつか注意を述べておく．

まず，合流性および連結的とは次のような性質である．

#definition[合流性，連結性][
  - 2項関係 $R$ が*合流的*#index(initial: (letter: "ご"))[合流的]であるとは次が成り立つことを言う．
    $
      forall x,y,z. [ x R y, x R z ==> exists u.[y R u, z R u]]
    $
  - 2項関係 $R$ が*連結的*#index(initial: (letter: "れ"))[連結的]であるとは次が成り立つことを言う．
    $
      forall x,y,z.[x R y, x R z ==> y R z || z R y]
    $
]

#definition[
  - $AxiomDot2 equiv dia box p -> box dia p$ #indexAxiom(display: $AxiomDot2$, name: ".2")
  - $AxiomDot3 equiv box (box p -> q) or box (box q -> p)$ #indexAxiom(display: $AxiomDot3$, name: ".3")
]

#fact[
  - $AxiomDot2$ は合流的なフレームクラスを規定する．
  - $AxiomDot3$ は連結的なフレームクラスを規定する．
]

#let LogicS4Dot2 = $Logic("S4.2")$
#let LogicS4Dot3 = $Logic("S4.3")$

#definition($LogicS4Dot2, LogicS4Dot3$)[
  - $LogicS4Dot2 := LogicS4 oplus AxiomDot2$ #indexLogic(display: $LogicS4Dot2$, name: "S4.2")
  - $LogicS4Dot3 := LogicS4 oplus AxiomDot3$ #indexLogic(display: $LogicS4Dot3$, name: "S4.3")
]

#fact[
  - $LogicS4Dot2$ は合流的な前順序のフレームクラスに対して健全かつ完全．
  - $LogicS4Dot3$ は連結的な前順序のフレームクラスに対して健全かつ完全．
]

ここで，合流性と連結性を弱めて，次のような性質を考える．
#definition[弱合流性，弱連結性][
  - 2項関係 $R$ が*弱合流的*#index(initial: (letter: "ご"), "合流的")[弱合流的]であるとは次が成り立つことを言う．
    $
      forall x,y,z. [ x R y, x R z, y != z ==> y R z || z R y]
    $
  - 2項関係 $R$ が*弱連結的*#index(initial: (letter: "れ"), "連結的")[弱連結的]であるとは次が成り立つことを言う．
    $
      forall x,y,z.[x R y, x R z, y != z==> y R z || z R y]
    $
]

#lemma[
  弱合流性は合流性より真に弱い性質である．
]
#proof[
  まず，フレームが合流的ならば弱合流的であることを示す．
  // TODO:
  次に弱合流的だが合流的でないフレームを構成して示す．
  // TODO:
]

同様に，

#lemma[
  弱連結性は連結性より真に弱い性質である．
]

#proof[
  まず，フレームが連結的ならば弱連結的であることを示す．
  // TODO:
  次に弱連結的だが連結的でないフレームを構成する．
  // TODO:
]

一方，次のことが成り立つ．

#lemma[
  $R$ が反射的なら，$R$ が弱合流的であることと合流的であることは同値であり，$R$ が弱連結的であることと連結的であることは同値となる．
]
#proof[
  // TODO:
]

#let AxiomDot2w = $Axiom(".2w")$
#let AxiomDot3w = $Axiom(".3w")$

#definition[
  - $AxiomDot2w equiv dia box (box p or q) -> box dia (dia p or q)$ #indexAxiom(display: $AxiomDot2w$, name: ".2w")
  - $AxiomDot3w equiv box (p and box p -> q) or box (q and box q -> p)$ #indexAxiom(display: $AxiomDot3w$, name: ".3w")
]

#lemma[
  - $AxiomDot2w$ は弱合流的なフレームクラスを規定する．
  - $AxiomDot3w$ は弱連結的なフレームクラスを規定する．
]
#proof[
  // TODO:
]


ここまでを踏まえると，次のことが言える．

#corollary[
  - $AxiomDot2w$ が規定するフレームクラスと $AxiomDot2$ が規定するフレームクラスは異なる．
  - $AxiomDot3w$ が規定するフレームクラスと $AxiomDot3$ が規定するフレームクラスは異なる．
  - ${AxiomT, AxiomDot2w}$ が規定するフレームクラスと ${AxiomT, AxiomDot2}$ が規定するフレームクラスは等しい．
  - ${AxiomT, AxiomDot3w}$ が規定するフレームクラスと ${AxiomT, AxiomDot3}$ が規定するフレームクラスは等しい．
]

#let LogicK4Dot2 = $Logic("K4.2")$
#let LogicK4Dot3 = $Logic("K4.3")$


一方 $AxiomT$ を含まない体系ならこの同値性は成り立たない．
そしてとても紛らわしいが，多くの文献において $LogicK4Dot2, LogicK4Dot3$ とは $LogicK4$ に $AxiomDot2, AxiomDot3$ を追加したもの*ではなく*，$AxiomDot2w, AxiomDot3w$ を追加した論理である．

#definition($LogicK4Dot2, LogicK4Dot3$)[
  - $LogicK4Dot2 := LogicK4 oplus AxiomDot2w$ #indexLogic(display: $LogicK4Dot2$, name: "K4.2")
  - $LogicK4Dot3 := LogicK4 oplus AxiomDot3w$ #indexLogic(display: $LogicK4Dot3$, name: "K4.3")
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

