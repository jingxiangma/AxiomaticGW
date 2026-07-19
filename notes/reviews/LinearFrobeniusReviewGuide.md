# Linear/Frobenius 检验顺序与 Lean 语法表

本文面向已经学完 `LeanZju/D1`，并准备阅读、检验和小范围修改 `AxiomaticGW/Linear` 与 `AxiomaticGW/Frobenius` 的读者。它不是通用 Lean 入门，而是这两个目录的工作手册。数学内容以 `notes/mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md` 为主，缝合的几何动机参考 `notes/mathematics/M02TwoDimensionalTFT.md` 第 2、3 节；精确的数学到 Lean 对照见 `notes/MathematicsToLean.md`。

## 1. 建议检验顺序

以下顺序服从实际导入依赖。每完成一个文件，先编译该文件并记录结论，再进入下一个文件。

| 顺序 | 文件 | 首要检验对象 |
| --- | --- | --- |
| 1 | `AxiomaticGW/Linear/PerfectPairing.lean` | `SymmetricPerfectPairing` 是否准确编码对称完美配对；`toDual` 是否与 `form x y` 的槽位约定一致 |
| 2 | `AxiomaticGW/Linear/Copairing.lean` | `tensorEndEquiv` 收缩哪一个张量因子；`copairing` 是否确由恒等映射反推；交换两个因子是否不变 |
| 3 | `AxiomaticGW/Linear/Contraction.lean` | `Fin 2` 两个节点槽、`S ⊕ Fin 2` 标签、非分离与分离收缩、换标及交换节点顺序是否一致 |
| 4 | `AxiomaticGW/Frobenius/Basic.lean` | `counit` 是否确实诱导 `counit (a * b)`；对称性和 Frobenius 不变性是否从交换律、结合律推出，而非作为冗余数据存储 |
| 5 | `AxiomaticGW/Frobenius/Constructions.lean` | 从不变完美配对恢复 `counit a = form a 1` 是否精确；`casimir`、`handleElement` 是否对应 M1 的约定 |
| 6 | `AxiomaticGW/Frobenius/Coalgebra.lean` | `comul a = (a ⊗ 1) * casimir` 的方向；Frobenius 关系、余单位律、余结合律、余交换律及 mathlib `Coalgebra` 打包 |
| 7 | `AxiomaticGW/Frobenius/Examples.lean` | 基环与乘积环是否真正满足完美性；显式 `casimir`、`comul`、`handleElement` 计算能否作为前六个文件的回归测试 |

这也是推荐的第一次阅读顺序。第二遍做项目集成检验时，应从下游反向回看：

1. `Linear/Contraction.lean` 进入 `TFT/Basic.lean`、`TFT/Sewing.lean`、
   `CohFT/Basic.lean`、`CohFT/Frobenius.lean`、`GW/Basic.lean` 和量子乘积代码。
2. `Frobenius/Constructions.lean` 的 `casimir` 与 `handleElement` 进入 TFT correlator
   和 sewing 公式。
3. `Frobenius/Examples.lean` 的 `baseRing` 被常值理论和 point-target 模型直接使用。
4. 修改基础声明后，至少编译直接使用它的文件；若签名、`[simp]`、实例或换标行为变化，运行完整
   `lake build`。

## 2. 检验的三个层次

不能只检查文件自身是否编译。应依次检查以下三层，而且编译通过只回答了其中很小一部分。

### 2.1 数学语义

对照 M1、M2，逐项写清对象、假设和结论，再读 Lean 类型。重点检查：

- `form x y` 与 `toDual x y` 的两个槽位有没有交换；
- `copairing` 采用哪一个 `V ⊗ V ≃ End(V)` 约定；
- 非分离缝合的两个节点是否确由 `Fin 2` 表示；
- 分离缝合中两个 `none` 是否分别变成 `0` 和 `1`；
- `Module.Free`、`Module.Finite` 只在有限自由对偶确实需要时出现；
- `CommRing`、交换 Frobenius 代数等假设是否与数学陈述相符；
- 零模、空标签类型、`Fin 0`、`Fin 1`、`Fin 2` 等边界情形是否仍有正确含义；
- 定理是否证明了注释声称的等式，而不是只证明一个较弱或换了方向的版本。

### 2.2 mathlib 表示与兼容性

这两个目录有意复用 mathlib 的 `LinearMap.IsPerfPair`、`Dual`、`TensorProduct`、 `MultilinearMap` 和 `Coalgebra`。检验时应确认：

- 项目没有重复实现已有 mathlib 概念；
- `SymmetricPerfectPairing` 是显式数据而非全局类型类，因为同一模可有多个配对；
- `F.toCoalgebra` 保持显式，只有需要时通过 `letI` 局部安装，避免非典范全局实例；
- `TensorProduct.assoc`、`lid`、`rid`、`comm` 的方向与 mathlib 定义一致；
- 证明优先使用公开定理，避免依赖定义展开后的偶然形状；
- `[simp]` 只标记规范、终止的化简方向；`@[ext]` 与 `@[reducible]` 不造成意外全局行为；
- 通过小型 `example` 从导入模块的用户视角测试 API，而不只在定义所在命名空间中测试。

查找 mathlib API 时，先用编辑器跳转、`#check`、`#print` 和仓库内 `rg`；确认没有现成声明后再加 helper lemma。

### 2.3 项目地位与下游行为

这些文件是 TFT、CohFT 和 GW 的基础层，改动的影响通常大于文件本身。特别检查：

- `selfContract`、`pairContract` 是 TFT/CohFT/GW gluing axiom 的表达工具；
- `selfContractTarget`、`pairContractTarget` 支持值域不是 `R` 的 CohFT/GW 类；
- 换标定理支撑有限标签的对称性和 WDVV 证明；
- `casimir`、`handleElement` 支撑 correlator 和 sewing 公式；
- `baseRing` 支撑常值理论和 point-target 回归例。

改变公有声明前必须运行类似下面的全项目搜索：

```bash
rg -n 'DeclarationName|related_term' AxiomaticGW AxiomaticGWTest
```

若只改证明而不改陈述，也要确认新证明没有依赖过宽的 simp 集或偶然导入。

## 3. 逐文件检查表

### `Linear/PerfectPairing.lean`

- `isPerfPair` 的数学含义应通过 mathlib 的定义核实，不要从名称猜测。
- `toDual` 使用 `letI` 临时提供已存储的完美性证明；确认没有把配对安装成全局实例。
- `toDual_apply` 固定本项目的槽位约定，是后续所有张量收缩的起点。
- 基础结构本身不应无故要求有限自由；该条件只在张量-Hom 等价处加入。

### `Linear/Copairing.lean`

- 展开纯张量公式，手算
  `tensorEndEquiv (x ⊗ₜ y) z = form x z • y`。
- 由该公式核实 `copairing_contract` 是正确的 snake identity。
- `copairing_comm` 需要配对对称性；检查证明没有偷用欲证结论。
- 明确有限自由假设来自 `dualTensorHomEquiv`，而不是来自完美配对的定义本身。

### `Linear/Contraction.lean`

- 分别测试标量值域与一般值域版本，并检查两者的一致性定理。
- 对 `separatingLabelsEquiv` 的四类输入逐一手算正向、逆向映射。
- 检查交换 `Fin 2` 后收缩不变，理由必须来自 copairing 对称性。
- 检查 `domDomCongr` 的等价方向；等价写反通常仍能产生看似合理的类型。
- 用 `S := Empty`、`S := Fin 1` 做 scratch 测试，暴露空槽和单槽错误。
- `pairContractTarget_comp_lift` 是 CohFT/GW 标量化的重要兼容性结果，修改 target-valued API
  时必须回归。

### `Frobenius/Basic.lean`

- 结构只存 `counit` 与 trace pairing 的完美性；检查没有遗漏真正独立的数据。
- `pairing.isSymm` 应来自 `mul_comm`，`pairing_assoc` 应来自 `mul_assoc`。
- `CommFrobeniusAlgebra.ext` 依赖 proof irrelevance；测试仅由 counit 相等即可得到结构相等。
- 有限自由条件不属于基本定义，因此不应提前加入。

### `Frobenius/Constructions.lean`

- 在 `invariant a b 1` 中逐步核实
  `form (a * b) 1 = form a b`，从而恢复原配对而非仅得到同构配对。
- `casimir` 只是 `F.pairing.copairing` 的 Frobenius 专用名称；避免出现第二套定义。
- `handleElement` 的因子顺序在交换代数中不敏感，但仍应与 M1 文档一致。

### `Frobenius/Coalgebra.lean`

- 从 `includeLeft_mul_casimir_eq_includeRight_mul_casimir` 开始检查，这是后续公式的核心平衡等式。
- 分别检查左右余单位律，不能只凭余交换性默认二者相同。
- 余结合等式含显式 `TensorProduct.assoc`，画出三重张量的括号方向再读证明。
- `toCoalgebra` 应填满 mathlib 的全部 law 字段；`toIsCocomm` 应在同一个局部实例下解释。
- 确认没有新增全局 `Coalgebra R A` 实例，因为 Frobenius functional 不是唯一的。

### `Frobenius/Examples.lean`

- 不只看结构字面量能否编译，要验证 perfectness 的单射和满射两部分。
- 对 `R × R` 用 `(1, 0)`、`(0, 1)` 手算 trace pairing、Casimir 和 comultiplication。
- 示例定理应足够精确地捕获约定错误；只证明存在性不能充当回归测试。

## 4. 本项目 Lean 语法表

### 4.1 文件、作用域与参数

| 语法 | 在本项目中的含义或用途 |
| --- | --- |
| `module` | 使用 Lean 4 的 module 文件模式；导入与可见性由后续声明控制 |
| `public import X` | 导入 `X`，并让本模块的使用者也获得该依赖的公开声明 |
| `@[expose] public section` | 本仓库 module 风格的公开声明区；不要随意删除或移动 |
| `namespace AxiomaticGW` | 把声明放入项目命名空间，避免与 mathlib 名称冲突 |
| `open TensorProduct` | 允许写较短名称；它不等于导入模块 |
| `variable {R V : Type*}` | 为一组声明预设隐式参数；花括号参数通常由 Lean 推断 |
| `[CommRing R]` | 类型类参数；Lean 自动搜索 `R` 的交换环结构 |
| `(P : SymmetricPerfectPairing R V)` | 普通显式参数，调用时必须给出或由点记法提供 |
| `(R := R)` | 命名参数，用于消除隐式参数推断歧义 |
| `section FiniteFree ... end FiniteFree` | 把额外假设限制在局部声明组中 |
| `omit [Module.Free R V] in theorem ...` | 指明该定理实际不依赖当前 section 中的某些类型类假设 |
| `noncomputable def` | 定义在经典选择或不可执行等价上是数学确定的，但不承诺可求值 |
| `letI : Coalgebra R A := F.toCoalgebra` | 仅在当前作用域安装一个局部类型类实例 |

参数括号应区分：

```lean
(x : V)                 -- 显式参数
{x : V}                 -- 隐式参数，由上下文推断
[Module R V]            -- 类型类隐式参数，由实例搜索
```

### 4.2 代数、线性映射与等价

| Lean | 数学含义 |
| --- | --- |
| `AddCommGroup V` | `V` 是加法交换群 |
| `Module R V` | `V` 是 `R`-模 |
| `Algebra R A` | `A` 是 `R`-代数，包含标量映入及兼容性数据 |
| `Module.Free R V` | `V` 是自由 `R`-模 |
| `Module.Finite R V` | `V` 是有限生成 `R`-模 |
| `V →ₗ[R] W` | `R`-线性映射 |
| `V ≃ₗ[R] W` | `R`-线性等价 |
| `A →ₐ[R] B` | `R`-代数同态 |
| `Dual R V` | 线性对偶 `V →ₗ[R] R` |
| `Module.End R V` | 线性自同态 `V →ₗ[R] V`，不是可逆自同构 |
| `LinearMap.BilinForm R V` | 双线性形式，底层是 `V →ₗ[R] V →ₗ[R] R` |
| `MultilinearMap R (fun i ↦ M i) W` | 输入类型由指标 `i` 决定的多线性映射 |
| `P.toDual x y` | 先把 `x` 送入对偶，再在 `y` 上求值 |
| `e.symm` | 等价 `e` 的逆方向 |
| `e.trans f` | 先应用 `e`，再应用 `f` |
| `f.comp g` | 先应用 `g`，再应用 `f` |
| `f.toLinearMap` | 从带更多结构的映射取其底层线性映射 |
| `F.pairing` | 点记法，通常等价于 `CommFrobeniusAlgebra.pairing F` |

`→ₗ` 与 `≃ₗ` 必须严格区分：前者只是保持线性结构的函数，后者还包含逆映射和互逆证明。

### 4.3 张量积记号与核心 API

| Lean | 数学含义或检查重点 |
| --- | --- |
| `V ⊗[R] W` | `R` 上的张量积 |
| `x ⊗ₜ[R] y` | 纯张量 `x ⊗ y` |
| `TensorProduct.lift f` | 由双线性映射 `f` 诱导的张量积上线性映射 |
| `TensorProduct.uncurry ...` | 把适当的 curried 线性映射变为张量积上的线性映射 |
| `TensorProduct.congr e₁ e₂` | 对两个张量因子分别应用线性等价 |
| `TensorProduct.comm R V W` | 交换两个张量因子 |
| `TensorProduct.assoc R U V W` | 张量积结合子；必须检查定义域和值域的括号方向 |
| `TensorProduct.lid R V` / `rid` | 左/右单位子，把 `R ⊗ V` 或 `V ⊗ R` 与 `V` 对应 |
| `LinearMap.rTensor` / `lTensor` | 在线性映射右侧/左侧保留一个张量因子 |
| `LinearMap.mul' R A` | 由乘法诱导的 `A ⊗[R] A →ₗ[R] A` |
| `Algebra.TensorProduct.includeLeft` | `a ↦ a ⊗ 1` |
| `Algebra.TensorProduct.includeRight` | `a ↦ 1 ⊗ a` |

证明一般张量等式时，本项目常用纯张量生成性：

```lean
induction t using TensorProduct.induction_on with
| zero => ...
| tmul x y => ...
| add t₁ t₂ h₁ h₂ => ...
```

三个分支分别验证零、纯张量和加法；必须确认 `tmul` 分支中的因子顺序。

### 4.4 有限标签与多线性映射

| Lean | 含义 |
| --- | --- |
| `Fin n` | 恰有 `n` 个元素的有限类型 |
| `Fin 2` | 两个有序节点槽，元素写作 `0`、`1` |
| `Option S` | `some s` 表示普通标签，`none` 表示新增节点标签 |
| `S ⊕ T` | 不交并；构造子是 `Sum.inl`、`Sum.inr`，常缩写为 `.inl`、`.inr` |
| `fun _ : S ↦ V` | 以 `S` 为指标的常值类型族，每个输入槽都是 `V` |
| `Fin.cons x (fun _ ↦ y)` | 构造 `Fin 2 → V`，第一个值为 `x`，其余值为 `y` |
| `f.currySum` | 把由 `S ⊕ T` 标记的输入按两组 curry |
| `f.domDomCongr e` | 用类型等价 `e` 重标记输入；重点核实 `e` 的方向 |
| `f.domCoprod g` | 合并两个多线性映射的输入并产生张量值域 |
| `φ.compMultilinearMap f` | 在线性目标映射 `φ` 前合成多线性映射 `f` |
| `fin_cases i` | 穷举 `Fin n` 的有限情况，适合检查 `Fin 1`、`Fin 2` |

模式匹配例子：

```lean
fun
  | .inl none => .inr 0
  | .inl (some s) => .inl (.inl s)
```

读这种代码时，应为每个构造子写出源类型和目标类型，不能只凭缩进判断嵌套层级。

### 4.5 结构、属性与全局行为

| 语法 | 用途与检验点 |
| --- | --- |
| `structure X ... where` | 声明记录类型；检查每个字段是否是必要且独立的数据 |
| `def x : X where ...` | 用命名字段构造结构 |
| `@[simp] theorem h ...` | 把 `h` 加入全局 simp 集；检查方向、终止性和下游影响 |
| `@[ext] theorem X.ext ...` | 注册外延定理，使 `ext` 可把结构相等化为字段相等 |
| `@[reducible] def` | 允许类型类合成等过程更积极展开定义；检查是否确有互操作需要 |
| `rfl` | 两边定义展开后相同；不表示数学结论“显然” |
| `by ...` | tactic 风格证明块 |
| `:= term` | 直接给出证明项或定义项 |

新增属性前，可先在 scratch 文件中比较带与不带该属性时的 `simp only`、`simp?` 和实例合成行为。

### 4.6 本目录高频证明模式

| 模式 | 作用 |
| --- | --- |
| `simp only [h₁, h₂]` | 只使用列出的规则化简，便于审计证明依赖 |
| `simpa only [...] using h` | 把已有证明 `h` 的类型受控化简为当前目标 |
| `rw [h]` / `rw [← h]` | 定向改写；检查等式方向 |
| `apply e.injective` | 通过单射 `e` 把原等式转为像的等式 |
| `apply LinearMap.ext; intro x` | 把线性映射相等化为逐点相等 |
| `ext x` | 使用已注册外延定理；事后确认选中了哪个 ext lemma |
| `congr 1` / `funext i` | 处理函数应用或函数相等；注意 `congr` 生成的目标 |
| `congrArg f h` | 对等式 `h` 两端应用同一函数 `f` |
| `congrArg₂ op h₁ h₂` | 对二元运算的两个参数分别使用等式 |
| `change newGoal` | 把目标改写成定义相等的形状，不会证明新的数学等式 |
| `induction t using TensorProduct.induction_on` | 通过零、纯张量、加法证明张量上的命题 |
| `rcases i with i | i <;> rfl` | 对和类型分情况并在各分支尝试反射性证明 |
| `ac_rfl` | 仅用结合律和交换律规范化；适合交换幺半群表达式 |

看到 unrestricted `simp`、`simp_all`、大范围 `unfold` 或重复 coercion 操作时，应先查明其成功原因， 再判断是否需要改为公开 API lemma 或 `simp only`。不要为了缩短证明而盲目替换已有透明证明。

## 5. 查询、scratch 检验与命令

### 5.1 常用查询

在临时 `.lean` 文件中可使用：

```lean
#check AxiomaticGW.SymmetricPerfectPairing
#check AxiomaticGW.SymmetricPerfectPairing.copairing_contract
#check AxiomaticGW.CommFrobeniusAlgebra.toCoalgebra
#print AxiomaticGW.CommFrobeniusAlgebra
#print axioms AxiomaticGW.CommFrobeniusAlgebra.coassoc
#synth Module ℤ ℤ
```

- `#check` 显示声明类型；必要时用 `#check @name` 暴露隐式参数。
- `#print` 显示定义或定理的详细信息。
- `#print axioms` 检查定理依赖的公理，重点排除 `sorryAx` 和意外项目公理。
- `#synth` 测试类型类实例能否被找到，也能暴露缺失或歧义实例。

不要把一次 `#synth` 成功当作实例设计正确；还要确认找到的是预期且典范的实例。

### 5.2 推荐 scratch 模板

在仓库根目录临时建立测试文件，验证后删除；有长期回归价值的例子应放入适当测试模块。

```lean
import AxiomaticGW.Frobenius.Examples
import AxiomaticGW.Linear.Contraction

namespace Scratch

open TensorProduct
open AxiomaticGW

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

example (P : SymmetricPerfectPairing R V) (x : V) :
    P.tensorEndEquiv P.copairing x = x := by
  exact P.copairing_contract x

example (R : Type*) [CommRing R] :
    (CommFrobeniusAlgebra.baseRing R).handleElement = 1 := by
  simp only [CommFrobeniusAlgebra.baseRing_handleElement]

end Scratch
```

### 5.3 每个文件的检验循环

```bash
git status --short
git diff --stat
git diff
rg -n '\b(sorry|admit)\b' AxiomaticGW/Linear AxiomaticGW/Frobenius
lake env lean AxiomaticGW/Linear/PerfectPairing.lean
```

把最后一条命令替换为当前文件。修改基础 API 后，再执行：

```bash
lake build
git diff --check
git diff --stat
git diff -- path/to/changed/files
```

建议为每个声明保留一份简短检验记录：数学公式、Lean 类型、所需假设、证明机制、下游使用者、 结论及严重级别。只有发现明确问题时才修改代码；修改应保持最小，并在同一轮更新相关回归例和文档。

## 6. 当前起点

开始正式逐文件检验前，应先把本文件当作路线图，而不是已经完成的审计结论。当前最合适的第一项工作是：

1. 精读 `Linear/PerfectPairing.lean`；
2. 用 `#print LinearMap.IsPerfPair` 和 `#print LinearMap.toPerfPair` 核实 mathlib 语义；
3. 在 scratch 中分别检查 `toDual_apply` 及零模/基环等简单实例；
4. 搜索 `SymmetricPerfectPairing` 的所有下游使用；
5. 形成该文件的 findings，再决定是否需要代码修改。
