# HarderNarasimhan 项目重构计划书

> 状态：**已完成**（2026-08-25）——阶段 0–11 全部实施完毕，见 `refactor` 分支上
> 首行为「阶段 n: …」的连续提交（阶段 0 `fa3bb37` 起，至阶段 11 收尾提交）。
> §8 的十二项设计决议已全部与作者讨论定案（2026-08-24）。
> 参考规范：
> [mathlib style guide](https://leanprover-community.github.io/contribute/style.html) ·
> [documentation style](https://leanprover-community.github.io/contribute/doc.html) ·
> [naming conventions](https://leanprover-community.github.io/contribute/naming.html)

---

## 0. 现状诊断

当前代码库为对应 Chen–Jeannin《Harder–Narasimhan Game》逐条编号而组织，存在以下工程问题：

1. **Defs/Impl/Results 三分**导致大量重复：同一事实在 `impl` 命名空间和公开命名空间各有一份
   （如 `ConvexI_top_iff_Convex`、`semistable_iff`、`μ_nonempty`、`dualμAstar_eq_μBstar` 均有两份）；
   公开层几乎全是薄包装。
2. **论文编号命名**（`lemma_2_4`、`prop3d8₁'`、`rmk4d10₂`）不自描述、不可检索，且公开语句是
   巨型合取（`proposition_2_6` 把 (2.4)、(a)、(b)、(c) 打包成一个嵌套 `∧`），下游只能用
   `.2.2.1` 之类的投影访问，极其脆弱。
3. **裸函数 `μ : Intvl ℒ → S`** 无法使用 dot notation，所有 API 以 `μmax μ`、`Resμ I μ` 前缀式
   出现；对偶化 `fun (p : Intvl ℒᵒᵈ) ↦ toDual (μ ⟨p.right, p.left, p.lt⟩)` 在四处内联重写。
4. **每条声明重复完整的 binder 望远镜**（`{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] …`），没有使用
   `variable`/`section`；且不少定义带了多余的实例假设（如 `μmax` 只需 `Preorder ℒ`，却要求
   `Nontrivial + PartialOrder + BoundedOrder`）。
5. **`Nat.find` + `open Classical` 泛滥**：三个 filtration 结构都用 `∃ n, … = ⊤` + `Nat.find`
   表达长度，迫使几乎每条相关声明 `open Classical in`；结构的后续字段类型依赖
   `Nat.find fin_len`，封装在定义处即泄漏；`Nat.find` 携带的决断性实例是藏在项里的数据，
   实例合成路径不同即不 defeq——`JordanHolderFiltration/Impl.lean:48` 的
   `attribute [-instance] Subtype.instDecidableEq` 补丁就是现成伤疤。
6. **`StI` 的嵌套存在式**导致证明里大量 `hxSt.out.choose_spec.choose` 链条，不可维护。
7. **Coprimary 模块的全局污染**：`ℒ`、`S`、`S₀`、`μ`、`_μ` 作为顶层 `abbrev`，以及
   `priority := 114514` 的高优先级 `LinearOrder (Finset …)` 实例，都是危险设计。
8. 语句里的 `------------` 分隔线、"API note:" 模板化 docstring 等格式噪音。

---

## 1. 重构目标与总原则

1. **取消 Defs/Impl/Results 三分**。每个主题一个（或少数几个）文件；重要的、被复用的结论
   （包括原 Impl 中被广泛使用者）直接以最终名字暴露；纯中间步骤用 `private` 或保留为
   文件内局部辅助引理。`impl` 命名空间整体删除。
2. **模仿 mathlib 的目录组织**：四大板块 `PayoffFunction/`、`Filtration/`、`JordanHolder/`、
   `Coprimary/`，加一个基础设施文件 `StrictIntvl.lean`（详见 §3）。
3. **`section` + `variable` 统一管理参数**，命名空间按类型组织（详见 §5）。
4. **将 payoff function 做成单字段结构 `PayoffFunction`**，全面启用 dot notation：
   `μ.max`、`μ.A`、`μ.restrict I`、`μ.IsSemistable`、`μ.HarderNarasimhanFiltration`……
   （详见 §2）。
5. **一条引理一个结论**：拆掉所有论文式巨型合取；论文编号只出现在 docstring 的引用中
   （`This is Proposition 3.8 of [ChenJeannin].`），不出现在声明名中。
6. **docstring 全部重写**（英文），遵循 mathlib doc style；每个文件带 `/-!` 模块文档
   （`# 标题`、`## Main definitions`、`## Main results`、`## References`）。
7. **最小化每条声明的假设**（利用工具逐条检查 `Nontrivial`/`BoundedOrder` 等是否真的需要）。
8. 不设 `@[deprecated]` 兼容别名（项目未发布、无下游），旧名直接消失。

**非目标**：不新增数学内容；不改变任何定理的数学强度；暂不向 mathlib 上游提交
（但把可上游的部分整理成自包含文件，见 §3 与 §9）。

---

## 2. 核心设计：`PayoffFunction` 结构

### 2.1 结构本体

采用 mathlib 打包态射的标准做法——**单字段结构 + `FunLike`**（而非 `abbrev` 类型同义词：
同义词一旦在归约中被展开，dot notation 与实例检索都会失效；结构最稳健）：

```lean
namespace HarderNarasimhan

/-- A *payoff function* on the strict intervals of `ℒ`, with values in `S`.
`μ ⟨a, b, h⟩` is the payoff of the game played on the interval `(a, b)`. -/
@[ext]
structure PayoffFunction (ℒ : Type*) [LT ℒ] (S : Type*) where
  /-- The underlying interval-indexed function. -/
  toFun : StrictIntvl ℒ → S

instance : FunLike (PayoffFunction ℒ S) (StrictIntvl ℒ) S where
  coe := PayoffFunction.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[simp] lemma coe_mk (f : StrictIntvl ℒ → S) : ⇑(⟨f⟩ : PayoffFunction ℒ S) = f := rfl
```

- 结构本体只要求 `[LT ℒ]`（`StrictIntvl` 的最低要求）；更强的假设放在各操作的
  section variable 上。
- 所有现有 `μ ⟨a, b, h⟩` 的调用形式经 `FunLike` 强制转换后语法不变。

### 2.2 导出操作全部收进 `PayoffFunction` 命名空间

关键决定：`max`/`min`/`A`/`B` **返回 `PayoffFunction`**（而不是裸函数）。
这样它们本身可继续被当作 payoff function 使用（现有代码里 `μmax μ` 正是这样用的），
并让"与限制交换"引理成为漂亮的结构等式。`A`/`B` 是选手专名（先手博弈值），
按【决议①】用大写单字母。

```lean
variable {ℒ : Type*} [Preorder ℒ] {S : Type*} [CompleteLattice S]

/-- `μ.max I` is the supremum of `μ (I.left, u)` over interior points `u ∈ (I.left, I.right]`. -/
def max (μ : PayoffFunction ℒ S) : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨆ u ∈ Set.Ioc I.left I.right, μ ⟨I.left, u, ‹_›.1⟩⟩

def min (μ : PayoffFunction ℒ S) : PayoffFunction ℒ S := …  -- 原 μmin

/-- `μ.A I`: the value of the game on `I` when player A moves first（原 μA，minimax）. -/
def A (μ : PayoffFunction ℒ S) : PayoffFunction ℒ S := …

/-- `μ.B I`: the value when player B moves first（原 μB，maximin）. -/
def B (μ : PayoffFunction ℒ S) : PayoffFunction ℒ S := …

/-- `μ.IsAttained I`: the infimum defining `μ.A I` is attained. -/
def IsAttained (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : Prop := …

/-- Restriction of `μ` to the points of `I`（原 `Resμ`）. -/
def restrict (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : PayoffFunction ↥I S := ⟨fun J ↦ μ ↑J⟩

/-- Order-dual payoff（把四处内联的 `fun p ↦ toDual (μ ⟨p.right, p.left, p.lt⟩)` 命名化）. -/
def dual (μ : PayoffFunction ℒ S) : PayoffFunction ℒᵒᵈ Sᵒᵈ := …
```

- **`μAstar`/`μBstar` 删除**【决议⑫】：一律写 `μ.A ⊤`、`μ.B ⊤`（比原名还短）。
- 补一组**基础 API 引理**，让下游永远不用手写 `le_iSup₂_of_le`/`iInf₂_le_of_le`：

```lean
lemma le_max (hu : u ∈ Set.Ioc I.left I.right) : μ ⟨I.left, u, hu.1⟩ ≤ μ.max I
lemma max_le (h : ∀ u (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩ ≤ s) : μ.max I ≤ s
-- 以及 min / A / B 的对应各组，@[simp] 视情况标注
lemma min_le_apply : μ.min I ≤ μ I        -- 原 rmk4d10₀ 左半
lemma apply_le_max : μ I ≤ μ.max I        -- 原 rmk4d10₀ 右半
```

- **限制交换引理**升格为结构等式（原 `μmax_res_intvl` 等）：

```lean
@[simp] lemma restrict_apply : μ.restrict I J = μ ↑J
@[simp] lemma max_restrict : (μ.restrict I).max = μ.max.restrict I
@[simp] lemma min_restrict : (μ.restrict I).min = μ.min.restrict I
@[simp] lemma A_restrict   : (μ.restrict I).A   = μ.A.restrict I
@[simp] lemma B_restrict   : (μ.restrict I).B   = μ.B.restrict I
```

  引理名以大写 `A` 开头符合 mathlib 惯例（引理名原样引用声明名，如 `Icc_subset_Icc`）。

- **对偶 API**（原 `dualμAstar_eq_μBstar` 等）：

```lean
@[simp] lemma dual_dual : μ.dual.dual = μ
@[simp] lemma A_dual : μ.dual.A = (μ.B).dual   -- 原引理仅在 ⊤ 处；结构版实现时验证，
@[simp] lemma B_dual : μ.dual.B = (μ.A).dual   -- 退路是 ⊤ 处的逐点版本
```

### 2.3 性质类（原各种 class）的处理

全部收进 `PayoffFunction` 命名空间、按 mathlib 命名规则改名，仍保持 **typeclass `Prop`**
（现有代码大量依赖实例链，如 `IsSlopeLike μ → IsSlopeLike (μ.restrict I)`、
`IsAffine → IsConvex`，运转良好）。使用规则统一为：

- **全局性质**（`IsConvex`、`IsSlopeLike`、`IsSemistable` 等）：以实例隐参 `[μ.IsConvex]`
  出现在用户可见定理中（当前 Results 层显式传 `hμcvx`、Filtration 层又用实例隐参，两种
  风格并存——统一为实例隐参）。
- **区间局部变体**（`IsConvexOn I` 这类含变动参数 `I` 者）：实例检索无法命中，作为
  显式假设传递。

**链条件家族按【决议④⑤】统一缩写风格**：`WeakACC` / `StrongDCC` / `EventuallyTopDCC` /
`ADCC`（docstring 写明全称与语义）。

| 现名 | 新名（`PayoffFunction` 命名空间内） | 备注 |
|---|---|---|
| `Convex μ` | `IsConvex` | class |
| `ConvexI I μ` | `IsConvexOn I` | class，但通常显式传 |
| `Convex_of_Convex_large` | `IsConvexOn.mono : I₂ ≤ I₁ → μ.IsConvexOn I₁ → μ.IsConvexOn I₂` | 假设改用 `StrictIntvl` 上现成的包含序！ |
| `SlopeLike μ` | `IsSlopeLike` | |
| `Semistable μ` | `IsSemistable` | 【决议】 |
| `Stable μ` | `IsStable`（仍 `extends IsSemistable`） | |
| `semistableI μ I` | **删除**，一律写 `(μ.restrict I).IsSemistable` | 原 `semistableI_iff` 变为 `breakpoints` 刻画引理 |
| `Affine μ` | `IsAffine`（移入 Convex 文件，`IsAffine → IsConvex` 实例随行） | |
| `NashEquilibrium μ` | `HasNashEquilibrium` | 【决议③】"博弈有值"；docstring 注明取值相等表述 |
| `μAdmissible μ` | `Admissible` | 【决议⑨】 |
| `FiniteTotalPayoff μ` | `FiniteTotalPayoff`（不动，仅入命名空间） | |
| `μA_DescendingChainCondition μ` | `ADCC` | 【决议⑤】关于 `μ.A` 的下降链条件 |
| `WeakAscendingChainCondition μ` | `WeakACC` | 【决议⑤】 |
| `StrongDescendingChainCondition μ` | `StrongDCC` | 【决议⑤】 |
| `StrongDescendingChainCondition' μ` | `EventuallyTopDCC` | 【决议④】docstring 写明语义是"∃ 某步 payoff = ⊤"（非 filter 意义的 eventually） |
| `WeakSlopeLike₁ μ` | `WeakSlopeLikeAtTop` | 上端点锚定在 `⊤`（非链条件，不缩写） |
| `WeakSlopeLike₂ μ` | `WeakSlopeLikeAtBot` | 下端点锚定在 `⊥` |

类字段名同步按 mathlib 风格重命名（字段名不重复类名、描述结论形状；逐一在实现时定）。

### 2.4 断点集（原 `S₁I`/`S₂I`/`StI`/`St`）重设计

现状是嵌套 `∃` 的集合定义，证明里全是 `.out.choose_spec.choose` 链。按【决议②】改为
**具名字段的 Prop 结构 + 集合**，这是本次重构最大的可维护性收益之一：

```lean
/-- `x` is a *breakpoint* of `μ` on `I`: among interior initial segments of `I`, `(I.left, x)`
maximises `μ.A`, and `x` is the greatest element doing so. -/
structure IsBreakpoint (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) (x : ℒ) : Prop where
  mem      : x ∈ I
  ne_left  : I.left ≠ x
  not_lt   : ∀ y (hy : y ∈ I) (h : I.left ≠ y), ¬ μ.A ⟨I.left, x, _⟩ < μ.A ⟨I.left, y, _⟩
  le_of_eq : ∀ y (hy : y ∈ I) (h : I.left ≠ y),
      μ.A ⟨I.left, y, _⟩ = μ.A ⟨I.left, x, _⟩ → y ≤ x

/-- The set of breakpoints of `μ` on `I`（原 `StI`）. -/
def breakpoints (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : Set ℒ := {x | μ.IsBreakpoint I x}
```

- 原 `S₁I`、`S₂I` 不再独立命名（成为字段 `not_lt`、`le_of_eq`）。
- 原 `St μ` 删除：写 `μ.breakpoints ⊤`。
- 提供 `IsBreakpoint.left_lt : I.left < x` 等便捷投影，杜绝 `lt_of_le_of_ne hxI.1 hx`
  的重复拼装。

### 2.5 区间类型：`Intvl` 改名 `StrictIntvl`【决议⑩】

- 结构（`left`/`right`/`lt`）、包含偏序、`⊤`、`↥I` 子类型及其实例、`ofSub`/`CoeOut` 全部
  保留，仅做 docstring 与假设最小化整理；类型与文件改名为 `StrictIntvl`（点明
  `left < right` 严格性，且不与 mathlib 的 `Interval` 撞名）。
- 成员名不变：`StrictIntvl.ofSub`、`StrictIntvl.mem_top`、`StrictIntvl.val_bot`……

---

## 3. 目录与文件组织

```
HarderNarasimhan.lean                    -- 库根：仅 re-export（umbrella import）
HarderNarasimhan/
  StrictIntvl.lean                       -- StrictIntvl、成员关系、包含序、⊤；点类型 ↥I 及其
                                         --   Nontrivial/Lattice/BoundedOrder/WellFoundedGT/
                                         --   IsModularLattice 实例；ofSub
  PayoffFunction/
    Defs.lean                            -- PayoffFunction 结构、FunLike/ext；max/min/A/B
                                         --   及其 le_/‗le API；IsAttained；dual 及对偶引理
    Restrict.lean                        -- restrict；restrict_apply、max_restrict 等交换引理
    Convex.lean                          -- IsConvex/IsConvexOn/IsAffine；原 §2 全部不等式
    SlopeLike.lean                       -- IsSlopeLike、seesaw 刻画与其推论（轻量 import）
    Slope.lean                           -- slope r d（原 μQuotient，重 import：ℝ/NNReal/Module）
                                         --   + (slope r d).IsSlopeLike
    Semistable/
      Defs.lean                          -- IsSemistable/IsStable、ADCC、IsBreakpoint/breakpoints、
                                         --   restrict 翻译引理（原 Translation.lean 吸收于此）
      Breakpoints.lean                   -- 原 §3：断点存在性（递归构造）、唯一性、全序性、
                                         --   greatest 元、prop 3.7/3.8 系列
    GameValue.lean                       -- WeakACC/StrongDCC/WeakSlopeLikeAtTop/AtBot 及实例；
                                         --   A ⊤ = min ⊤、B ⊤ = max ⊤、先手优势（原 §4.1–4.4）
    NashEquilibrium.lean                 -- HasNashEquilibrium；原 4.10–4.21 全部结果
  Filtration/
    Defs.lean                            -- Admissible；HarderNarasimhanFiltration 结构（§4 新设计）
                                         --   + length API；semistableRel（原 IntervalSemistableRel）
    Exists.lean                          -- 规范构造 μ.hnFiltration（原 HNFil）、Inhabited 实例
    Unique.lean                          -- 线性序下唯一性（原 theorem3d10）、Unique 实例、
                                         --   RelSeries 打包（存在 + 唯一）
  JordanHolder/
    Defs.lean                            -- FiniteTotalPayoff、EventuallyTopDCC、
                                         --   JordanHolderFiltration 结构 + length API、jordanHolderRel
    Exists.lean                          -- 构造（原 JHFil）+ Nonempty 实例 + RelSeries 打包
    Stability.lean                       -- step 条件 ↔ 逐段 Stable（原 *_of_step_cond₂ 系列）
    Length.lean                          -- 模格下长度唯一（含 subseqIdx 机器，标 private）
  Coprimary/
    AssociatedPrimes.lean                -- 纯交换代数（Bourbaki IV §1 no.2 Prop.6 商侧），
                                         --   自包含，mathlib 上游候选（原 CommutativeAlgebra.lean）
    Defs.lean                            -- 值域（Colex + DedekindCut）、Coprimary.payoff、
                                         --   IsCoprimary、CoprimaryFiltration 结构 + length API
    Semistability.lean                   -- A 的显式计算、凸性、DCC、
                                         --   IsSemistable ↔ ∃! associated prime（原 3.11–3.14）
    Filtration.lean                      -- CoprimaryFiltration 的存在与唯一（原 3.15）
DependencyExtractor.lean                 -- 保留（开发工具；可选：移入 scripts/）
```

要点：

- 原 `Basic.lean` 拆解：`Intvl` 部分归 `StrictIntvl.lean`，`μmax` 等归
  `PayoffFunction/Defs.lean`。
- 原 `FirstMoverAdvantage/` 与 `NashEquilibrium/` 并入 `PayoffFunction/`（它们是 payoff
  function 的博弈值理论，正对应方案中 (2a) "讨论它不同的条件及性质"）。
- 每个文件 **import 最小化**（mathlib 原则）：`SlopeLike.lean` 不再连带 `ℝ`/`NNReal`
  （这正是拆出 `Slope.lean` 的原因）；`StrictIntvl.lean` 只依赖少量 Order 文件。
- 预期依赖链（左 → 右）：
  `StrictIntvl → PF.Defs → PF.Restrict → {Convex, SlopeLike} → Slope`,
  `Convex → Semistable.Defs → Semistable.Breakpoints`,
  `{SlopeLike, Restrict} → GameValue → NashEquilibrium`,
  `Semistable → Filtration`, `{NashEquilibrium, Convex, Semistable} → JordanHolder`,
  `{Filtration, AssociatedPrimes} → Coprimary`。
  注意 **JordanHolder 不依赖 Filtration**（与现状一致）。

---

## 4. Filtration 结构重设计：显式 `length` 字段【决议⑥：方案 A，已经作者审阅定稿】

三个 filtration 结构（HN、JordanHolder、Coprimary）现用 `fin_len : ∃ n, f n = ⊤` +
`Nat.find`，是 `open Classical` 泛滥、字段类型泄漏 `Nat.find`、决断性实例不匹配
（`Subtype.instDecidableEq` hack）的共同根源。改为**把长度作为数据**（对标 mathlib 的
`RelSeries`/`CompositionSeries`——mathlib 从不用"`ℕ → α` + 存在性"编码有限链）。
已审阅通过的定义：

```lean
/-- A **Harder–Narasimhan filtration** for the payoff function `μ`: a finite chain
`⊥ = F 0 < F 1 < ⋯ < F F.length = ⊤`, extended constantly by `⊤` above `length`, whose
successive steps are semistable and whose `μ.A`-slopes strictly decrease.

`length` is stored as data but carries no extra information: it is provably the *least*
index at which the chain reaches `⊤` (`length_le_of_eq_top`), hence determined by `toFun`;
accordingly `ext` only asks for `toFun` to agree. -/
structure HarderNarasimhanFiltration (μ : PayoffFunction ℒ S) where
  /-- The underlying chain; apply via the coercion, `F n`. -/
  toFun : ℕ → ℒ
  /-- The index at which the chain reaches `⊤`. -/
  length : ℕ
  monotone : Monotone toFun
  head_eq_bot : toFun 0 = ⊥
  length_eq_top : toFun length = ⊤
  strictMonoOn : StrictMonoOn toFun (Set.Iic length)
  /-- Each successive step `(F i, F (i + 1))` is semistable. -/
  piecewise_isSemistable : ∀ i, (hi : i < length) →
    (μ.restrict ⟨toFun i, toFun (i + 1), strictMonoOn hi.le hi (lt_add_one i)⟩).IsSemistable
  /-- Successive `μ.A`-slopes strictly decrease, in the `¬ · ≤ ·` sense appropriate for a
  possibly non-linear codomain `S`. -/
  not_A_le_succ : ∀ i, (hi : i + 1 < length) →
    ¬ μ.A ⟨toFun i, toFun (i + 1),
        strictMonoOn (Nat.le_of_succ_le hi.le) hi.le (lt_add_one i)⟩ ≤
      μ.A ⟨toFun (i + 1), toFun (i + 2), strictMonoOn hi.le hi (lt_add_one (i + 1))⟩
```

配套 API（`FunLike`、极小性两行定理、手写 `ext`）：

```lean
instance : FunLike (μ.HarderNarasimhanFiltration) ℕ ℒ where …

lemma ne_top_of_lt (h : m < F.length) : F m ≠ ⊤ := …         -- 由 strictMonoOn 推出
lemma length_le_of_eq_top (h : F m = ⊤) : F.length ≤ m := …  -- 极小性是定理不是公理
lemma eq_top_of_length_le (h : F.length ≤ m) : F m = ⊤ := …

@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := …
  -- length 由极小性相等；其余字段 proof irrelevance
```

要点：

- `strictMonoOn hi.le hi (lt_add_one i)` 的成员关系拼装与现在逐字相同（`i < length` 与
  `i + 1 ≤ length` 在 `ℕ` 上 defeq 的技巧照旧），构造侧证明可近乎原样搬运。
- 结构定义、字段访问、下游陈述全程无 `Nat.find`、无 `open Classical`；
  `attribute [-instance] Subtype.instDecidableEq` hack 预期随之删除（实现时验证）。
- `Unique` 证明里 `Nat.find hffin` 与 `a.length` 的换算全部消失；`RelSeries` 互转
  （对方也是 `length` + `toFun`）从"证 `Nat.find hstrange = F1.length`"变成字段直搬。
- 构造侧（`Exists.lean`）在**一处**用 `Nat.find` 算出最小长度，之后封在字段里。
- `JordanHolderFiltration`（antitone 版：`head_eq_top`/`length_eq_bot`、
  `step_payoff_eq`/`payoff_lt_of_between`）与 `CoprimaryFiltration` 同构改造。

公开入口改进【决议⑦】：规范 HN filtration 从"`default`（`Inhabited` 实例）"升格为具名定义
（对标 `Measure.rnDeriv`/`fderiv` 的高频 term 级缩写先例）：

```lean
noncomputable def PayoffFunction.hnFiltration (μ : PayoffFunction ℒ S)
    [μ.ADCC] [μ.IsConvex] [μ.Admissible] : μ.HarderNarasimhanFiltration
```

`Inhabited`/`Unique` 实例由它派生（`⟨μ.hnFiltration⟩` 一行）。JordanHolder 侧无唯一性，
保留 `Nonempty` 实例即可。

---

## 5. 命名空间与 `variable` 约定

- 全库仍在根命名空间 `HarderNarasimhan` 中；`StrictIntvl`、`PayoffFunction` 及其子结构各开
  `namespace`。文件骨架统一为：

```lean
namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Lattice ℒ] [BoundedOrder ℒ] [Nontrivial ℒ]
variable {S : Type*} [CompleteLattice S]
variable {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

section Convex
…
end Convex

end PayoffFunction

end HarderNarasimhan
```

- 需要更弱假设的段落另开 `section` 局部声明（如 `Preorder ℒ` 段、`CompleteLinearOrder S` 段），
  **不**为迁就少数声明抬高整个文件的假设。
- 类型变量沿用 `ℒ`（格）与 `S`（值域）——unicode 变量 mathlib 允许（如 `𝕜`），且全库一致；
  模块变量沿用 `R`、`M`。
- `A`/`B` 作为选手专名用大写 def 名；引用它们的引理名以大写字母开头
  （`A_restrict`、`inf_A_le_A_sup`），这与 mathlib 引理名原样引用声明名的惯例一致
  （如 `Icc_subset_Icc`）。
- 假设命名遵循 mathlib：`h`、`hxy`、`hμ` 等小写；不再出现 `inst_3`、`this'''`、`h₁₅` 这类
  机器名残留（实现时顺手清理）。
- 语句中不再用 `(hx : ⊥ < x) → …` 依赖箭头去给结论中要引用的假设命名——重构后结论
  用 `StrictIntvl` 值或由 API 引理承担，普通 `→` 即可。

---

## 6. 语句与证明风格规范（实现时逐条执行）

1. **拆合取**：`proposition_2_6`、`remark_4_10`、`proposition_3_8`、`NashEquil_equiv` 等
   一律拆成单结论引理。
2. **TFAE 政策【决议⑪】**：工作 API 一律用成对具名 iff（下游禁用 `TFAE.out` 下标提取）；
   仅 Nash 章的 4 项等价链保留一条 `nashEquilibrium_tfae` 作总览（由 iff 两行拼出）；
   3 项的两处（原 `prop4d16₁`、`remark_3_14`）不保留 TFAE。
3. **删除编号名**：`lemma_2_4`/`prop3d8₁'`/`rmk4d10₂` → 描述性名（对照表见 §7）；docstring 中
   注明 `This is Lemma 2.4 of [ChenJeannin]`，并在各文件 `## References` 与根 README 建立
   论文对照总表。
4. **格式**：删除语句内 `------------` 分隔线；100 列；`↦`；`:=` 与 `where` 位置、缩进等
   按 style guide；保持 `weak.linter.mathlibStandardSet = true` 通过。
5. **docstring**：英文完整句；定义讲"是什么 + 记号约定"，定理讲"内容 + 关键假设为何需要"；
   删除现有空洞的 "API note: this is the main user-facing …" 模板句（有实质内容者保留改写）。
6. **`simp` 集合审计**：现有 `@[simp]`（如 `relSeries_step_lt`）逐一复核；新增的
   `restrict_apply`、`*_restrict`、`coe_mk` 等按 simp normal form 原则标注。
7. **实例命名**：匿名实例保持匿名；需要引用的实例给 mathlib 式名字。
8. `open Classical` 仅限证明内 `classical` tactic；`open … in` 尽量消除（§4 已除去主要来源）。
9. **`seesaw'` 拆为 iff 族**【与作者讨论定案】：seesaw 的本质是固定 `x < y < z` 后三个
   两两比较互为等价，故正确拆法不是九条单向蕴含，而是 `<`/`>`/`=` 三种关系 × 两两位置的
   **可 `rw` 的 iff 引理**（6–9 条，各 1–2 行，均由三歧性推出）；三歧性
   `IsSlopeLike.seesaw`（增/减/常三选一）保留为旗舰总览。下游 `(seesaw' …).2.2.1` 式
   数字投影全部消失（现约 10 处调用点几乎都是单投影，bundle 的摊销收益并不存在）。
   该族引理统一加 **`seesaw_` 名字前缀**（留在 `PayoffFunction` 命名空间内，保住 μ-dot
   notation：`μ.seesaw_lt_left_iff h₁ h₂`），避免 `open` 后与序论基本引理混淆；
   尾部用 `left`/`total`/`right` 指 `x<y<z` 上的 `μ(x,y)`/`μ(x,z)`/`μ(y,z)`，
   约定写进模块 docstring。

---

## 7. 全量迁移对照表

约定：省略命名空间前缀时，新名均位于 `HarderNarasimhan.PayoffFunction`（或注明的其他
命名空间）内；"private" 表示保留为文件内部辅助（不承诺稳定 API）；"删除" 表示其内容被
吸收/内联。中间引理的最终定名在实现时按 naming convention 微调，下表给出基准方案。

### 7.1 Basic.lean / Interval.lean → `StrictIntvl.lean` + `PayoffFunction/{Defs,Restrict}.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `Intvl` 及其全部成员引理/实例 | `StrictIntvl.lean`，类型改名 `StrictIntvl`【决议⑩】，成员名不变（假设最小化 + docstring 重写） |
| `Intvl.ofSub`、`ofSub_left/right/top`、`CoeOut` | `StrictIntvl.ofSub` 等，不变 |
| `Intvl.val_bot` / `val_top` | 不变（移入 `StrictIntvl` 命名空间声明处集中） |
| `μmax` / `μmin` / `μA` / `μB` | `max` / `min` / `A` / `B`【决议①】（均返回 `PayoffFunction`） |
| `μAstar` / `μBstar` | 删除【决议⑫】；写 `μ.A ⊤` / `μ.B ⊤` |
| `IsAttained` | `IsAttained`（dot notation：`μ.IsAttained I`） |
| `Resμ` | `restrict` |
| `μ_res_intvl` | `restrict_apply`（`@[simp]`） |
| `μmax_res_intvl` … `μB_res_intvl` | `max_restrict` / `min_restrict` / `A_restrict` / `B_restrict`（结构等式，`@[simp]`） |
| （新增） | `dual`、`dual_dual`、`A_dual`、`B_dual`；`le_max`/`max_le` 等 8 条基础 API |

### 7.2 Convexity/ → `PayoffFunction/Convex.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `Convex` / `ConvexI` / `Convex_of_Convex_large` | `IsConvex` / `IsConvexOn` / `IsConvexOn.mono`（见 §2.3） |
| `impl.ConvexI_top_iff_Convex` + 公开重复 + 两个转换实例 | `isConvexOn_top_iff`（`@[simp]`）+ 双向实例各一 |
| `ConvexI_iff_Convex_res` | `isConvexOn_iff_isConvex_restrict` |
| `impl.lem2d4₁` | `A_le_max_inf`（无凸性假设的那条） |
| `impl.lem2d4₂I` | `IsConvexOn.max_inf_le_max` |
| `impl.lem2d4₃I` | `IsConvexOn.A_le_A_sup` |
| `impl.lem2d4I`、`lemma_2_4` | 删除（合取打包层；三条组件引理即为公开 API） |
| `impl.rmk2d5₁` | `IsConvexOn.max`（`μ.max` 继承局部凸性；可做实例） |
| `impl.rmk2d5₂` | `IsConvexOn.max_max`（`μ.max.max I = μ.max I` 方向按 simp normal form 定） |
| `impl.rmk2d5₃` | `IsConvexOn.A_max`（`μ.max.A I = μ.A I`） |
| `remark_2_5` | 删除（打包层） |
| `impl.prop2d6₀` | `A_anti_left`（左端点反单调；无凸性） |
| `impl.prop2d6₁I` | `IsConvexOn.inf_le_A` |
| `impl.prop2d6₂I₁` / `₂I₂` | `IsConvexOn.A_eq_of_ge` / `IsConvexOn.A_le_A_of_lt`（拆两条） |
| `impl.prop2d6₃I` | `IsConvexOn.A_eq_or_lt`（保留二择一形式） |
| `proposition_2_6` | 删除（打包层） |
| `impl.rmk2d7`、`remark_2_7` | `IsConvex.A_right_eq_of_A_left_gt`（线性序特化，一条） |
| `impl.prop2d8₀I` | private |
| `impl.prop2d8₁I` | `IsConvexOn.inf_A_le_A_sup` |
| `impl.prop2d8₂I`、`proposition_2_8` | `IsConvexOn.A_le_A_sup_or`（打包层删除） |
| `Affine`（自 JordanHolder/Defs 迁来） | `IsAffine` + `IsAffine → IsConvex` 实例 + restrict 实例 |

### 7.3 Semistability/ → `PayoffFunction/Semistable/{Defs,Breakpoints}.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `μA_DescendingChainCondition` | `ADCC`【决议⑤】 |
| `S₁I` / `S₂I` / `StI` / `St` | `IsBreakpoint`（结构，§2.4）/ `breakpoints`；`St` 删除【决议②】 |
| `semistableI` | 删除（写 `(μ.restrict I).IsSemistable`） |
| `Semistable` / `Stable` | `IsSemistable` / `IsStable` |
| `impl.semistable_iff`（+ Translation 重复） | `isSemistable_iff_right_mem_breakpoints_top` 之类的刻画引理（一份） |
| `impl.semistableI_iff`（+ Translation 重复） | `isSemistable_restrict_iff`（restrict 与 breakpoints 的翻译，一份） |
| `impl.prop3d2`、`proposition_3_2` | `IsConvexOn.A_le_of_A_eq_top`（一份，放 Convex 或此处视依赖而定） |
| `impl.cor3d3`、`corollary_3_3`（alias） | `adcc_of_forall_exists_A_eq_top`（构造子引理，一份） |
| `impl.ℒₛ`、`prop3d4₀func` 及其 6 条 defprop/len 引理 | private（`improvingSet`、`breakpointAux` 等内部名） |
| `impl.prop3d4`、`proposition_3_4` | `breakpoints_nonempty`（存在性主定理） |
| `impl.rmk3d5`、`remark_3_5` | `IsBreakpoint.eq`（线性序下唯一）或 `breakpoints_subsingleton` |
| `impl.prop3d7₁` | `IsBreakpoint.isSemistable_restrict` |
| `impl.prop3d7₂` | `IsBreakpoint.not_A_le`（断点之上不再被支配） |
| `proposition_3_7` | 删除（打包层） |
| `impl.prop3d8₁` | `breakpoints_total`（`Std.Total` 实例化引理） |
| `impl.prop3d8₁'` | `exists_isGreatest_breakpoints` |
| `impl.prop3d8₂` | `IsBreakpoint.A_eq_A_of_lt`（分解公式） |
| `proposition_3_8` | 删除（打包层） |

### 7.4 SlopeLike/ → `PayoffFunction/{SlopeLike,Slope}.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `SlopeLike` | `IsSlopeLike` |
| `impl.prop4d6`、`seesaw` | `isSlopeLike_iff_seesaw`（iff 一份）+ 正向便捷版 `IsSlopeLike.seesaw` |
| `seesaw'` | 删除，代之以 `seesaw_` 前缀的 iff 族（§6.9）：如 `seesaw_lt_left_iff : μ ⟨x,y⟩ < μ ⟨x,z⟩ ↔ μ ⟨x,z⟩ < μ ⟨y,z⟩` 等（`<`/`>`/`=` × 两两位置，尾部名实现时定） |
| `μQuotient` | `slope r d`（`PayoffFunction.slope`；度/秩之商，DedekindCut 值域） |
| `impl.μQuotient_helper` | private |
| `impl.principal_lt_top` | `DedekindCut.principal_lt_top`（放独立小节，mathlib 上游候选） |
| `impl.prop4d8`、`SlopeLike_of_μQuotient` | `isSlopeLike_slope`（一份；可做实例） |
| restrict 实例 | 保留：`IsSlopeLike (μ.restrict I)` |

### 7.5 FirstMoverAdvantage/ → `PayoffFunction/GameValue.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `WeakAscendingChainCondition`（+ WF 实例） | `WeakACC`【决议⑤】 |
| `StrongDescendingChainCondition` | `StrongDCC`【决议⑤】 |
| `WeakSlopeLike₁` / `WeakSlopeLike₂`（+ 两个 SlopeLike 实例） | `WeakSlopeLikeAtTop` / `WeakSlopeLikeAtBot` |
| `impl.prop4d1_badSet`、`prop4d1₁_seq`、`prop4d1_helper`、`prop4d3_helper` | private |
| `impl.prop4d1₁`（+ `proposition_4_1` 前半） | `A_top_eq_min_top` |
| `impl.prop4d1₂`（+ 后半） | `A_top_le_B_top`（先手优势） |
| `impl.dual_wacc_of_sdcc` / `dual_wsl₁_of_wsl₂` | `μ.dual` 上的实例（`WeakACC μ.dual` 等） |
| `impl./公开 dualμAstar_eq_μBstar`、`dualμBstar_eq_μAstar` | 并入 §7.1 的 `A_dual`/`B_dual` |
| `impl.prop4d3₁`、`proposition_4_3` | `B_top_eq_max_top` |
| `impl.rmk4d4`、`remark_4_4` | `strongDCC_of_wellOrderedRank`（构造子，一份） |

### 7.6 NashEquilibrium/ → `PayoffFunction/NashEquilibrium.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `NashEquilibrium` | `HasNashEquilibrium`【决议③】 |
| `impl.rmk4d10₀`、`μmin_lt_μ_lt_μmax`（名实不符：实为 `≤`） | 拆为 `min_le_apply` / `apply_le_max`（移 §7.1 Defs） |
| `impl.rmk4d10₁` | `B_le_A_iff` |
| `impl.rmk4d10₂` / `rmk4d10₃` | `hasNashEquilibrium_iff_min_le` / `hasNashEquilibrium_iff_max_le`（名字实现时细化） |
| `remark_4_10` | 删除（打包层） |
| `impl.prop4d11₁` / `prop4d11₂`、`proposition_4_11` | `B_le_A_of_min_eq_max` / 逆向 `min_eq_max_of_B_le_A`（打包层删除） |
| `impl.prop4d12` / `prop4d14`、`proposition_4_12/14` | `min_eq_max_of_max_eq` / `max_eq_min_of_min_eq`（各一份） |
| `impl.rmk4d13` / `rmk4d15`、`remark_4_13/15` | 为上两条提供假设的两条 `IsSlopeLike.…` 小引理，或内联为带 `[IsSlopeLike]` 的推论 |
| `impl.prop4d16₁`、`proposition_4_16` | **不留 TFAE**【决议⑪】：拆为两条 iff（`max_top_eq_iff_min_top_eq` 等） |
| `impl.prop4d16₂` | `min_eq_max_iff_hasNashEquilibrium` |
| `impl.prop4d18₁` / `prop4d18₂`、`proposition_4_18` | `IsSemistable.B_le_A` / `IsSemistable.hasNashEquilibrium` |
| `impl.prop4d20`、`proposition_4_20` | `isSemistable_of_hasNashEquilibrium` |
| `impl.thm4d21`、`NashEquil_equiv` | 工作 API 为上述 iff 引理；额外保留 `nashEquilibrium_tfae`（4 项总览，由 iff 拼出）【决议⑪】 |

### 7.7 Filtration/ → `Filtration/{Defs,Exists,Unique}.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `μAdmissible`（+ CLO 实例） | `Admissible`【决议⑨】 |
| `HarderNarasimhanFiltration` | `μ.HarderNarasimhanFiltration`（类型全称【决议⑦】），字段重设计（§4）：`filtration → toFun`、新增 `length`、`first_eq_bot → head_eq_bot`、`fin_len` 删除（`length_eq_top` 成字段）、`strict_mono → strictMonoOn`、`piecewise_semistable → piecewise_isSemistable`、`μA_pseudo_strict_anti → not_A_le_succ` |
| `length` / `filtration_length` / `ne_top_of_lt_length` / `length_le_of_eq_top` | `length`/`length_eq_top` 成字段；后两者保留为两行定理 |
| `IntervalSemistableRel` | `semistableRel`（`μ.semistableRel`） |
| `impl.HNFil` 及 `HNFil_*` 系列、`HNlen` | private（`Exists.lean` 内部） |
| `instInhabitedHarderNarasimhanFiltration` | `μ.hnFiltration`（具名规范构造【决议⑦】）+ `Inhabited` 实例一行 |
| `impl.theorem3d10` | private（或 `HarderNarasimhanFiltration.eq_hnFiltration`），对外以 `Unique` 实例呈现 |
| `instUniqueHarderNarasimhanFiltration` | 保留（匿名实例） |
| `impl.relSeries_step_lt` / `relSeries_succ_step_lt` / `relSeries_strictMono` | `RelSeries` 辅助引理，检查 `@[simp]` 合理性后保留 |
| `impl.hHFil_of_hNSeries` | private |
| `exists_relSeries_isIntervalSemistable`（+ `…_of_completeLinearOrder`） | `exists_relSeries_semistableRel` / `existsUnique_relSeries_semistableRel` |

### 7.8 JordanHolderFiltration/ → `JordanHolder/{Defs,Exists,Stability,Length}.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `FiniteTotalPayoff`（+ restrict 实例） | 入命名空间；restrict 实例保留 |
| `StrongDescendingChainCondition'`（+ 2 实例） | `EventuallyTopDCC`【决议④】；到 `StrongDCC` 与 restrict 的实例保留 |
| `JordanHolderFiltration` | `μ.JordanHolderFiltration`（类型全称【决议⑦】），字段重设计（§4，antitone 版）；`step_cond₁ → step_payoff_eq`、`step_cond₂ → payoff_lt_of_between`（定名实现时细化） |
| `JordanHolderRel` | `jordanHolderRel` |
| `Affine` 及其实例 | 迁往 Convex（§7.2） |
| `impl.JHFil` 及 `JHFil_*`、`JH_pos_len` | private（`Exists.lean`；`length_pos` 作为结构引理公开） |
| `Nonempty` 实例 | 保留 |
| `exists_JordanHolderSeries` | `exists_relSeries_jordanHolderRel` |
| `impl.exists_next_lt`、`subseqIdx` 全家（8 条） | private（`Length.lean`；泛型 ℕ-antitone 链工具，mathlib 上游候选，见 §9） |
| `impl.μA_eq_μmin` | `IsSlopeLike.min_eq_A`（公开：桥接引理，多处可用） |
| `impl.μ_bot_JH_eq_μ_tot` | `JordanHolderFiltration.apply_payoff_eq_top_payoff`（实现时定名） |
| `impl.semistable_of_step_cond₂` / `stable_of_step_cond₂` / `step_cond₂_of_stable`、`piecewise_stable_iff` | `Stability.lean`：一条 iff + 两方向（打包层删除） |
| `impl.semistable_resμ_of_jordanHolderFiltration` | private |
| `IsModularLattice ↥I` 实例 | 移入 `StrictIntvl.lean` |
| `impl.induction_on_length_of_JordanHolderFiltration` | private |
| `length_eq_of_JordanHolderFiltration` | `JordanHolderFiltration.length_eq`（模格下长度唯一，主定理） |
| 文件头 `attribute [-instance] Subtype.instDecidableEq` | 预期随 §4 重设计删除（实现时验证） |

### 7.9 CoprimaryFiltration/ → `Coprimary/{AssociatedPrimes,Defs,Semistability,Filtration}.lean`

| 现名 | 去向 / 新名 |
|---|---|
| `S₀ R` + 3 个 priority-114514 实例 | **删除**：直接用 `Finset.Colex (LinearExtension (PrimeSpectrum R))`（mathlib 自带 `LinearOrder`，无须任何自定义实例/优先级 hack）；如需缩写，`abbrev PrimeColex R`（局部） |
| `S₀_order` / `S₀_order'` | 换成 mathlib `Finset.Colex` 现成引理（`toColex_le_toColex_of_subset`、`singleton_le_singleton`）+ 必要的薄引理 |
| `S R` + `Coe` | 删除 abbrev，值域内联写 `DedekindCut (PrimeColex R)` |
| `ℒ R M` | **删除**，写 `Submodule R M` |
| `Coprimary` | `IsCoprimary`（Prop 类命名规范；同时腾出 `Coprimary` 作命名空间名） |
| `μ R M` | `Coprimary.payoff R M : PayoffFunction (Submodule R M) …`【决议⑧】 |
| `_μ R M` | `Coprimary.assPrimes I`（Set 版）【决议⑧】；`Fintype` 实例保留 |
| `CoprimaryFiltration` 及 length API | 保留名字；字段重设计（§4）；`piecewise_coprimary`、`strict_anti_associated_prime` 字段名微调 |
| `CommutativeAlgebra.*`（4 条 + 主定理） | `AssociatedPrimes.lean`；命名空间改为按主词组织（如 `associatedPrimes_quotient_ker_mkLinearMap` 置于根），mathlib 上游候选 |
| `impl.μ_nonempty`（+ 公开重复） | `Coprimary.assPrimes_nonempty`（一份） |
| `impl.associatedPrimes_subset_of_submoduleOf_le` | 公开（通用交换代数小引理，或并入 AssociatedPrimes.lean） |
| `impl._μ_mono_right` | `Coprimary.assPrimes_mono_right` |
| `impl.μmax_eq_μ`（+ 公开重复） | `Coprimary.max_payoff`（`(payoff R M).max = payoff R M`，一份） |
| `impl.prop3d11`、`proposition_3_11` | `IsConvex` 实例一枚（匿名） |
| `impl.min'_asIdeal_mem` / `toLinearExtension_eq_min'` / `prop3d12p1` / `prop3d12p2` | private |
| `impl.lift_quot`（+ middle/not_bot）、`quotLiftQuotEquiv`、`locKer`、`associatedPrimes_quot_lift_locKer`、`quotEquivMapComap`、`map_comap_ne_bot`、`_mu_eq_quot_mu` | private（构造机器） |
| `impl.prop3d12`、`proposition_3_12` | `Coprimary.A_payoff`（`A = {min'}` 显式计算，主引理，一份） |
| `impl.prop3d13₁/₂`、`proposition_3_13` | WF 直接引用 mathlib 实例；DCC 保留为匿名实例（打包层删除） |
| `impl.rmk4d14₁` | `Coprimary.isSemistable_iff_A_const` |
| `impl.rmk4d14₂` | `Coprimary.isSemistable_iff_existsUnique_associatedPrime`（**核心语义定理**） |
| `remark_3_14`（TFAE） | **不留 TFAE**【决议⑪】：以上两条 iff 即为全部 API |
| `impl.quot_ntl` | private 或小引理公开 |
| `impl.muA_eq_quot_muA` / `semistable_res_iff_semistable_quot` | `Coprimary.A_restrict_eq_quotient` / `Coprimary.isSemistable_restrict_iff_quotient`（翻译层，公开） |
| `impl.piecewise_coprimary` | `HarderNarasimhanFiltration.piecewise_isCoprimary` |
| `Inhabited`/`Nonempty`/`Unique` 实例、`theorem_3_15₁/₂` | 实例保留（匿名）；编号包装删除；补具名 `Coprimary.coprimaryFiltration R M` 规范构造（与 `hnFiltration` 风格一致） |
| `impl.CoprimaryFiltration.toHarderNarasimhanFiltration` / `filtration_eq_harderNarasimhan_filtration` | `CoprimaryFiltration.exists_hnFiltration` / private |

### 7.10 根文件与杂项

| 现名 | 去向 |
|---|---|
| `HarderNarasimhan.lean` | 更新为新文件清单的 umbrella import |
| `HarderNarasimhan/Basic.lean` | 删除（内容按 §7.1 拆分） |
| `Semistability/Translation.lean` | 删除（吸收进 Semistable/Defs） |
| `DependencyExtractor.lean` | 保留；重构完成后重跑生成 `HarderNarasimhan.json` |
| `README.md` | 全面改写（新结构、新入口、论文对照表） |
| `prompt-doc.md`、`refactor.md` | 归档或删除（建议移入 `docs/` 或直接删除，git 历史留存） |

---

## 8. 决议纪要（原开放问题，已全部与作者定案，2026-08-24）

| # | 议题 | 决议 |
|---|---|---|
| ① | 原 `μA`/`μB` 命名 | **`μ.A` / `μ.B`**（选手专名大写；引理名以 `A`/`B` 原样入名） |
| ② | 断点术语（原 `StI`） | **`IsBreakpoint` / `breakpoints`**（Prop 结构 + 集合，§2.4） |
| ③ | Nash 类名 | **`HasNashEquilibrium`**（docstring 注明取"值相等"表述） |
| ④ | 原 `StrongDescendingChainCondition'` | **`EventuallyTopDCC`**（docstring 写明 ∃-步语义） |
| ⑤ | 原 `μA_DescendingChainCondition` 与链条件家族 | **`ADCC`，且全家统一缩写**：`WeakACC` / `StrongDCC` / `EventuallyTopDCC` / `ADCC` |
| ⑥ | filtration 长度表示 | **方案 A：显式 `length` 数据字段**（§4 的定义已经作者审阅通过） |
| ⑦ | HN/JH filtration 类型名 | **类型用全称** `HarderNarasimhanFiltration` / `JordanHolderFiltration`（mathlib 惯例：类型不缩写）；**规范构造用缩写** `μ.hnFiltration`（对标 `rnDeriv`/`fderiv` 的 term 级先例） |
| ⑧ | Coprimary 的 payoff 名 | **`Coprimary.payoff R M`**（`IsCoprimary` 腾出命名空间）；Set 版 `Coprimary.assPrimes` |
| ⑨ | 原 `μAdmissible` | **`Admissible`**（`[μ.Admissible]`） |
| ⑩ | `Intvl` 改名 | **`StrictIntvl`**（含文件名；点明严格性，避开 mathlib `Interval`） |
| ⑪ | TFAE 政策 | **工作 API 全部用具名 iff；仅 Nash 4 项链保留一条 `nashEquilibrium_tfae` 总览**；原 3 项两处（`prop4d16₁`、`remark_3_14`）不留 TFAE |
| ⑫ | `μAstar`/`μBstar` | **删除**，写 `μ.A ⊤` / `μ.B ⊤` |

---

## 9. 实施步骤

原则：**在专用分支上按 import 拓扑序逐模块迁移，每个阶段结束 `lake build` 必须全绿**、
linter（`weak.linter.mathlibStandardSet`）无新告警、无 `sorry`/新公理。不设兼容 shim——
每阶段把下游对旧名的引用一并机械更新（编译器驱动）。

| 阶段 | 内容 | 预估规模 |
|---|---|---|
| 0 | 开分支 `refactor`；提交本计划书 | — |
| 1 | `StrictIntvl.lean`（合并原 Basic 的 Intvl 部分与 Interval.lean；改名 `StrictIntvl`；假设最小化） | 小 |
| 2 | `PayoffFunction/Defs.lean` + `Restrict.lean`（结构、`max`/`min`/`A`/`B`、`dual`、基础 API）；全库改用 `PayoffFunction`——**这是最大的一次波及**，本阶段允许下游文件仅做机械适配（`μmax μ` → `μ.max` 等），不改名不拆分 | 大 |
| 3 | `Convex.lean`（合并三文件、改名、拆合取、吸收 `IsAffine`） | 中 |
| 4 | `Semistable/`（`IsBreakpoint` 重设计是难点：`.choose` 链换成字段访问） | 大 |
| 5 | `SlopeLike.lean` + `Slope.lean`（含 seesaw' 拆分及下游投影改写） | 中 |
| 6 | `GameValue.lean`（dual API 落地；链条件类改缩写名） | 中 |
| 7 | `NashEquilibrium.lean`（TFAE → iff 化） | 中 |
| 8 | `Filtration/`（§4 结构重设计在此落地；`hnFiltration`） | 大 |
| 9 | `JordanHolder/`（同步结构重设计；1100 行 Impl 的拆分与清理；验证删除 `Subtype.instDecidableEq` hack） | 大 |
| 10 | `Coprimary/`（Colex 去 hack、`IsCoprimary`/`Coprimary.payoff`、结构重设计） | 大 |
| 11 | 根文件、README 改写、重跑 DependencyExtractor、删除遗留文件、全库 docstring 终审 | 中 |

每阶段一个（或少数几个）commit，commit message 注明"阶段 n"。阶段 2 与 4/8/9 之间
如出现证明性能问题（`FunLike` 展开、simp 集变动），优先用 `simp only [restrict_apply, …]`
规范化，不引入 `attribute [-instance]` 类 hack。

**验证清单**（每阶段）：`lake build` 全绿；对抽查的代表性定理跑公理审计
（期望仅 `propext`、`Classical.choice`、`Quot.sound`）；linter 无新告警。
**收尾额外项**：README 论文对照表（论文编号 → 新声明名）作为编号名删除后的检索入口。

### mathlib 上游候选（重构后另行处理，不阻塞本重构）

- `Coprimary/AssociatedPrimes.lean`：Bourbaki IV §1 no.2 Prop.6 的商侧，完全自包含。
- `DedekindCut.principal_lt_top`（线性序群中主割严格小于 ⊤）。
- `subseqIdx` 机器：把"最终到 ⊥ 的 antitone ℕ-链"规范化为严格递减子链的通用构造。
- `StrictIntvl.lean` 中 `↥I` 的 `IsModularLattice`/`WellFoundedGT` 继承实例（mathlib 或已有
  `Set.Icc` 版本，实现时先查重）。

---

## 10. 风险与缓解

1. **`FunLike` 强制转换的摩擦**：`μ ⟨a,b,h⟩` 变成 `⇑μ ⟨a,b,h⟩`，个别 `rfl`/`simp` 证明
   可能失效。缓解：`coe_mk`、`restrict_apply` 等 `@[simp]` 引理先行到位；阶段 2 单独成段，
   问题集中暴露。
2. **结构重设计（§4）改变了构造证明的形状**：`Nat.find` 相关引理（`HNFil_ne_top_iff_lt_len`
   等）需要改写成 length 最小性引理。缓解：构造内部仍可局部使用 `Nat.find`，只是不进结构。
3. **实例链断裂**：改名后 `IsSlopeLike (μ.restrict I)` 等实例的 head symbol 变化，
   个别 `inferInstance` 需要显式化。编译器会逐一指出。
4. **工作量**：全库 ~7.5k 行全部触碰。按 §9 分 11 个可独立验证的阶段推进，任何阶段
   可暂停且库保持可用。

---

## 附录：docstring 模板

```lean
/-!
# Semistability for payoff functions

This file defines semistability and stability of a payoff function `μ : PayoffFunction ℒ S`,
the breakpoint predicate `PayoffFunction.IsBreakpoint`, and proves existence of breakpoints
under the descending chain condition `PayoffFunction.ADCC`.

## Main definitions

* `PayoffFunction.IsSemistable` : no proper initial segment beats the total interval.
* …

## Main results

* `PayoffFunction.breakpoints_nonempty` : existence of breakpoints (Proposition 3.4 of
  [ChenJeannin]).

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/
```

定理级 docstring：首句陈述结论本身（完整句、可独立阅读），随后一段解释关键假设/与论文的
出入；不写空洞的 "API note"。

