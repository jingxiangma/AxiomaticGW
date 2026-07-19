# `PerfectPairing.lean` 完整验证说明

本文记录对 `AxiomaticGW/Linear/PerfectPairing.lean` 的定向审查、测试设计、实际编译结果，以及以后可以重复使用的验证流程。对应的长期回归测试是：

```text
AxiomaticGWTest/Linear/PerfectPairing.lean
```

本次审查没有修改 `PerfectPairing.lean`。审查结论是：该文件的结构、假设、`toDual` 定义和槽位约定与项目 M1 数学说明以及 `Copairing.lean` 的下游用法一致。

## 1. `PerfectPairing.lean` 的整体结构

源文件按以下顺序组织。

### 1.1 `module`

文件开头的：

```lean
module
```

表示该文件使用 Lean 4 的模块系统。

### 1.2 公共导入

```lean
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
```

第一个 import 提供：

- `LinearMap.BilinForm`；
- `LinearMap.BilinForm.IsSymm`；
- 对称双线性形式的相关公开 API。

第二个 import 提供：

- `LinearMap.IsPerfPair`；
- `LinearMap.toPerfPair`；
- `LinearMap.toLinearMap_toPerfPair`；
- 完美配对诱导对偶等价的相关 API。

测试文件只直接导入 `AxiomaticGW.Linear.PerfectPairing`，因此可以检查这个模块能否独立作为公共入口使用，避免高层模块的传递导入掩盖依赖问题。

### 1.3 模块文档

模块文档说明这是 CohFT 状态空间上度量的一个小型 bundled interface，并解释了：

- `R V : Type*`；
- 方括号中的类型类参数；
- `Module R V`；
- `V →ₗ[R] W`；
- `V ≃ₗ[R] W`；
- `structure`；
- `noncomputable`。

文档与实际声明一致，没有夸大已经形式化的内容。

### 1.4 公共 section 和 namespace

```lean
@[expose] public section

namespace AxiomaticGW

open Module
```

`@[expose] public section` 表明后续声明属于模块公共接口。`namespace AxiomaticGW` 决定核心结构的完整名称是：

```lean
AxiomaticGW.SymmetricPerfectPairing
```

`open Module` 使文件中可以把 `Module.Dual R V` 简写为 `Dual R V`。

### 1.5 核心结构

```lean
structure SymmetricPerfectPairing (R V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] where
  form : LinearMap.BilinForm R V
  isSymm : form.IsSymm
  isPerfPair : form.IsPerfPair
```

三个字段分别表示：

1. `form` 是配对 `V × V → R`；
2. `isSymm` 证明 `form x y = form y x`；
3. `isPerfPair` 证明配对诱导的左右两个对偶映射都是双射。

### 1.6 派生定义和定理所在的 namespace

```lean
namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
```

因此后续声明支持点记法：

```lean
P.toDual
P.toDual_apply
```

接下来只有两个核心公共声明：

```lean
noncomputable def toDual ...

@[simp]
theorem toDual_apply ...
```

本文件没有给 `SymmetricPerfectPairing` 添加 `@[ext]`。`@[ext]` 出现在 mathlib 的 `LinearMap.IsPerfPair` 上，而不是这里的核心结构上。本文件新增的主要全局属性是 `toDual_apply` 上的 `[simp]`。

## 2. 核心声明之间的依赖关系

```text
LinearMap.BilinForm R V
        │
        ├── IsSymm
        └── IsPerfPair
               │
               ▼
SymmetricPerfectPairing R V
        │
        ├── form
        ├── isSymm
        └── isPerfPair
               │ 通过局部 letI 交给 mathlib
               ▼
          P.form.toPerfPair
               │
               ▼
       P.toDual : V ≃ₗ[R] Dual R V
               │
               ▼
 P.toDual_apply : P.toDual x y = P.form x y
               │
               ▼
 Copairing.tensorEndEquiv_tmul
```

数学上，`form` 是：

\[
\eta:V\times V\to R.
\]

`isSymm` 表示：

\[
\eta(x,y)=\eta(y,x).
\]

mathlib 的 `LinearMap.IsPerfPair` 要求两个诱导映射都双射：

\[
x\longmapsto (y\longmapsto\eta(x,y)),
\qquad
y\longmapsto (x\longmapsto\eta(x,y)).
\]

`toDual` 是第一个诱导映射形成的线性等价：

\[
\eta^\sharp:V\xrightarrow{\sim}V^\vee,
\qquad
\eta^\sharp(x)(y)=\eta(x,y).
\]

### 2.1 字段是否冗余

`isSymm` 和 `isPerfPair` 都依赖同一个 `form`，不是三个互不相干的数据。在已经知道对称性的情况下，左右诱导映射相同，所以 `IsPerfPair` 中右映射双射可由左映射双射推出。

这不构成结构缺陷：

- 项目直接复用了 mathlib 的标准 `LinearMap.IsPerfPair`；
- `isSymm` 和 `isPerfPair` 都是 `Prop` 中的证明；
- 它们不会产生两套可能互相矛盾的计算数据；
- 完整的 `IsPerfPair` 可以直接使用 mathlib 的公开 API。

### 2.2 槽位约定

`toDual_apply` 明确规定：

```lean
P.toDual x y = P.form x y
```

即：

```text
toDual x = fun y ↦ form x y
```

`Copairing.lean` 的下游公式是：

```lean
P.tensorEndEquiv (x ⊗ₜ[R] y) z = P.form x z • y
```

因此：

- `toDual` 作用在张量第一因子 `x`；
- 测试向量 `z` 进入 `form` 的第二槽；
- 所得标量作用在第二张量因子 `y`。

这与数学说明中的逆度量恒等式一致：

\[
\sum_i\eta(u_i,x)v_i=x.
\]

因为结构强制配对对称，所以也总能推出：

```lean
P.toDual x y = P.form y x
```

因此，对称具体实例的数值计算不能独自发现两个槽是否在定义中写反。必须同时检查：

1. `toDual_apply` 的 theorem statement；
2. `P.toDual.toLinearMap = P.form`；
3. `tensorEndEquiv_tmul`；
4. `copairing_contract` 的下游收缩公式。

## 3. 如何逐项检查核心 `structure`

在 scratch 区域先写：

```lean
#check AxiomaticGW.SymmetricPerfectPairing
#check @AxiomaticGW.SymmetricPerfectPairing
```

需要逐项确认：

1. `R V : Type*` 是结构的显式类型参数；
2. `[CommRing R]` 是类型类参数；
3. `[AddCommGroup V]` 提供加法群；
4. `[Module R V]` 提供 `R`-模结构；
5. `form` 实际是 curried 双线性映射 `V →ₗ[R] V →ₗ[R] R`；
6. `isSymm` 的数学内容是 `∀ x y, form x y = form y x`；
7. `isPerfPair` 包含左右两个诱导映射的双射性；
8. 没有 `Module.Free`、`Module.Finite`、`Nontrivial` 或 `Nonempty` 假设。

该结构是普通 structure 而不是 typeclass，因为同一个模块可能有多个不同配对，Lean 不应全局猜测使用哪个配对。

它没有重复定义 mathlib 已有的完整 bundled object：mathlib 提供 `LinearMap.IsPerfPair` 这一性质和 `toPerfPair`，而项目增加的是“对称双线性形式及其证明”的明确对象封装。

### 3.1 Command + 点击、`#check` 和 `#print`

在 VS Code 中按住 Command 点击 `LinearMap.IsPerfPair`，会跳到 mathlib 的 `LinearAlgebra/PerfectPairing/Basic.lean`。重点查看：

```lean
class IsPerfPair ... where
  bijective_left ...
  bijective_right ...
```

再点击 `form.IsSymm`，重点查看：

```lean
protected eq : ∀ x y, B x y = B y x
```

在 scratch 中还可以写：

```lean
#check LinearMap.IsPerfPair
#check @LinearMap.IsPerfPair
#print LinearMap.IsPerfPair
```

三者分工不同：

- Command + 点击：定位源码、文档和邻近 API；
- `#check`：验证当前 import 环境中名称可访问并查看类型；
- `#check @name`：显示通常被隐藏的隐式参数和类型类参数；
- `#print`：查看结构字段或定义体。

它们不能互相完全替代。尤其不能把 `#print` 展开的内部 record 表示当作长期稳定 API。公共声明类型、有文档的投影、公开定理和规范 `[simp]` 规则通常比具体定义展开更稳定。

## 4. 如何检查 `toDual`

先只看声明：

```lean
#check @AxiomaticGW.SymmetricPerfectPairing.toDual
```

确认输入和输出是：

```lean
P : SymmetricPerfectPairing R V
⊢ V ≃ₗ[R] Module.Dual R V
```

再在 scratch 中查看定义体：

```lean
#print AxiomaticGW.SymmetricPerfectPairing.toDual
```

定义的核心是：

```lean
letI : P.form.IsPerfPair := P.isPerfPair
exact P.form.toPerfPair
```

需要确认：

1. 定义域是 `V`；
2. 值域是 `Module.Dual R V`；
3. 使用了 `P.form` 和 `P.isPerfPair`；
4. `P.isSymm` 不参与构造 `toDual`；
5. `letI` 只在这个 `by` block 中有效；
6. 定义结束后不会留下全局 `P.form.IsPerfPair` 实例；
7. `toPerfPair` 使用的是第一槽诱导映射；
8. 没有增加有限或自由类型类假设。

不应随意建立全局实例，因为 `P` 是显式选择，同一个 `V` 可能有多个配对。全局实例会使类型类搜索承担非规范选择，并可能产生重叠或歧义。局部 `letI` 精确表达“本次使用这个配对的完美性”。

检查 mathlib 的 `toPerfPair` 时，可以 Command + 点击或使用：

```lean
#check @LinearMap.toPerfPair
#print LinearMap.toPerfPair
```

还应查看其公开求值定理：

```lean
p.toPerfPair x y = p x y
```

只看声明类型适合检查参数和假设；Command + 点击适合查来源和相关 API；`#print` 适合确认当前定义是否使用 `letI`；抽象 `example` 适合验证外部调用；具体实例适合验证计算、符号和边界行为。

## 5. 如何检查 `toDual_apply`

先写：

```lean
#check @AxiomaticGW.SymmetricPerfectPairing.toDual_apply
```

完整类型等价于：

```lean
∀ {R V}
  [CommRing R]
  [AddCommGroup V]
  [Module R V]
  (P : SymmetricPerfectPairing R V)
  (x y : V),
  P.toDual x y = P.form x y
```

数学公式是：

\[
\eta^\sharp(x)(y)=\eta(x,y).
\]

检查顺序应当是：

1. 抄出完整 Lean 类型；
2. 翻译成数学公式；
3. 检查变量和假设；
4. 检查等式左右两边都是 `R`；
5. 检查定理方向是从派生构造规范化到原始 `form`；
6. 检查 `x` 是第一槽、`y` 是第二槽；
7. 然后才读证明；
8. 检查是否使用过宽的 simp；
9. 检查证明所需定理来自哪个 import；
10. 搜索所有下游使用点。

实际证明是：

```lean
simp only [toDual, LinearMap.toLinearMap_toPerfPair]
```

这是受控的 `simp only`，没有依赖整个全局 simp 集。所用 mathlib 定理由直接 import 提供。

全项目搜索命令是：

```bash
rg -n "toDual_apply" AxiomaticGW AxiomaticGWTest
```

实际下游包括：

- `Linear/Copairing.lean`；
- `Linear/Contraction.lean`；
- `TFT/Sewing.lean`；
- `TFT/Classification.lean`；
- `CohFT/Frobenius.lean`；
- `GW/SmallQuantumProduct.lean`；
- `GW/BigQuantumProduct.lean`。

Lean 编译通过只说明 proof term 符合 theorem type。它不能自动保证 theorem type 就是作者想表达的数学结论。一个方向写反、假设不合理或结论过弱的 theorem 仍可能正确编译。因此必须先检查 statement，再检查 proof。

## 7. 每段测试的作用

### 7.1 导入和模块设置

```lean
import AxiomaticGW.Linear.PerfectPairing
```

只导入被测模块，检查其独立公共接口。

```lean
set_option linter.privateModule false
```

测试声明故意不成为公共库 API。关闭这一条不适用于回归测试模块的 linter，比把测试 fixture 标成 public 更合适。

```lean
noncomputable section
```

`toDual` 是非计算性线性等价，测试中直接构造或返回该数据，因此测试 section 同样声明为 noncomputable。

### 7.2 最小假设

抽象测试的变量声明固定 `toDual` 和 `toDual_apply` 所需的最小假设：

```lean
[CommRing R]
[AddCommGroup V]
[Module R V]
```

没有：

```lean
[Module.Free R V]
[Module.Finite R V]
```

测试文件直接构造零模例子，因此也会在 elaboration 时检查所需的环、加法群和模实例能够自动合成，不需要把探索性的 `#check`、`#print` 或 `#synth` 命令保留在长期测试中。

### 7.3 抽象公共 API 测试

抽象 examples 检查：

- `form` 的输入输出；
- `isSymm`、`isPerfPair` 与同一 `form` 的关系；
- `toDual` 的定义域和值域；
- 一次应用得到 dual，两次应用得到标量；
- 点记法；
- 完整限定名；
- `toDual.toLinearMap = form`；
- 由完美性得到的单射性；
- `toDual.symm` 的逆映射行为；
- 通过 `letI` 使用 mathlib `IsPerfPair` API。

由于这些 examples 只带最小三项类型类假设，它们也是防止以后误加 `Module.Free` 或 `Module.Finite` 的长期回归测试。

### 7.4 槽位测试

核心测试是：

```lean
example : P.toDual x y = P.form x y := P.toDual_apply x y
```

更强的线性映射测试是：

```lean
example : P.toDual.toLinearMap = P.form := by
  ext u v
  exact P.toDual_apply u v
```

反向公式的 example 是为了明确记录对称性会掩盖槽位错误，而不是把反向公式当作定义约定。

### 7.5 零模边界测试

`Fin 0 → R` 是零模。零双线性形式对称，且其左右诱导映射都在单元素类型之间，所以双射。该例验证：

- 可从模块外构造结构；
- 字段类型准确；
- `toDual` 适用于零维边界；
- `toDual_apply` 给出正确的具体计算；
- 没有隐藏的非零假设。

没有在本测试中重新构造基环和 `R × R` 配对，因为这会重复 Frobenius 示例中的较长完美性证明，或迫使测试导入更高层模块。基环和乘积代数更适合由 `Frobenius.Examples` 验证；这里使用抽象测试加零模边界保持模块隔离。

## 8. 在 VS Code 中从零复现

### 第一步：阅读源文件整体结构

打开：

```text
AxiomaticGW/Linear/PerfectPairing.lean
```

从上到下标记：

1. `public import`；
2. 模块 docstring；
3. `@[expose] public section`；
4. `namespace AxiomaticGW`；
5. `open Module`；
6. `structure SymmetricPerfectPairing`；
7. 嵌套 `namespace SymmetricPerfectPairing`；
8. `variable`；
9. `noncomputable def toDual`；
10. `@[simp] theorem toDual_apply`。

先画出 `form → isSymm/isPerfPair → toDual → toDual_apply` 的依赖关系，再进入 proof。

### 第二步：检查 structure

在 scratch 中写：

```lean
#check AxiomaticGW.SymmetricPerfectPairing
#check @AxiomaticGW.SymmetricPerfectPairing
#check @AxiomaticGW.SymmetricPerfectPairing.form
#check @AxiomaticGW.SymmetricPerfectPairing.isSymm
#check @AxiomaticGW.SymmetricPerfectPairing.isPerfPair
```

逐项核对显式类型参数、隐式参数、类型类参数、字段类型、数学含义、字段依赖、假设强弱、为何不是 typeclass，以及是否复用 mathlib 概念。

Command + 点击 `LinearMap.IsPerfPair` 和 `form.IsSymm`，结合 `#check @...` 与临时 `#print` 阅读 mathlib API。

### 第三步：检查 def

写：

```lean
#check @AxiomaticGW.SymmetricPerfectPairing.toDual
#print AxiomaticGW.SymmetricPerfectPairing.toDual
```

核对定义域、值域、用到的字段、`letI` 的局部作用域、没有全局实例、槽位顺序和最小类型类假设。再跳转到 `LinearMap.toPerfPair`，确认其求值约定。

### 第四步：检查 theorem

写：

```lean
#check @AxiomaticGW.SymmetricPerfectPairing.toDual_apply
```

先把类型翻译为 `η♯(x)(y)=η(x,y)`，检查两边类型、方向、变量、假设和槽位。然后阅读 `simp only` proof，并运行：

```bash
rg -n "toDual_apply" AxiomaticGW AxiomaticGWTest
```

检查全部下游用法。

### 第五步：从空测试文件逐段编写

新建：

```text
AxiomaticGWTest/Linear/PerfectPairing.lean
```

先写最小文件：

```lean
module

import AxiomaticGW.Linear.PerfectPairing

namespace AxiomaticGWTest
namespace LinearPerfectPairing

#check AxiomaticGW.SymmetricPerfectPairing

end LinearPerfectPairing
end AxiomaticGWTest
```

保存并编译。成功后依次加入：

1. `#check @SymmetricPerfectPairing`；
2. 三个字段的 `#check`；
3. `toDual` 与 `toDual_apply`；
4. 抽象变量；
5. 字段类型 examples；
6. `toDual` 值域 examples；
7. 点记法和完整限定名；
8. 线性映射等式；
9. 单射和逆映射；
10. 局部 `letI`；
11. 槽位限制；
12. 零模边界实例。

每加一小组就重新单文件编译。

### 第六步：观察错误、修正并完成验证

在 VS Code 中：

- 红色波浪线表示语法、elaboration 或类型错误；
- 鼠标停留查看简要诊断；
- Lean Infoview 查看完整目标和局部上下文；
- `unknown identifier` 时检查 import 和 namespace；
- `failed to synthesize` 时检查缺少的类型类；
- 点记法失败时先改用完整限定名；
- 参数顺序不清楚时用 `#check @完整名称`；
- simp 行为不透明时改成 `simp only [...]`。

最后依次运行：

```bash
lake env lean AxiomaticGW/Linear/PerfectPairing.lean
lake env lean AxiomaticGWTest/Linear/PerfectPairing.lean
lake env lean AxiomaticGW/Linear/Copairing.lean
lake build AxiomaticGWTest.Linear.PerfectPairing
lake test
lake build
```

## 9. 各种验证方法的作用和边界

### 9.1 Command + 点击

帮助定位源码、文档、namespace 和邻近 API。它不验证当前测试 import 环境能否访问名称，也不会自动完整展示隐式参数。

### 9.2 `#check`

验证名称可访问，并显示 Lean 推导后的声明类型。

### 9.3 `#check @name`

额外显示隐式类型参数、类型类参数和真实参数顺序，特别适合发现意外新增的 `Module.Free`、`Module.Finite`。

### 9.4 `#print`

适合查看结构字段或当前定义体。正式回归测试不应依赖定义展开后的不稳定细节，也不应保留大量探索性 `#print`。

### 9.5 抽象 `example`

验证最小假设、类型类推导、点记法、参数顺序、公共定理和普通下游证明是否可用，是 API 回归测试的主体。

### 9.6 具体实例 `example`

适合发现计算方向、符号、单位元、零对象和边界行为。但本结构强制对称，所以具体值不能独自区分两个槽位。

### 9.7 单文件编译

验证语法、import、elaboration、proof term 和该文件中的类型类合成。它不能保证 theorem statement 表达了作者真正想要的数学结论，也不能检查未编译下游。

### 9.8 全项目搜索

用于发现全部下游依赖、重复定理、约定传播和 API 修改影响范围。

### 9.9 `lake build`

验证默认库目标的完整依赖图。它能发现跨模块接口破坏，但不能代替数学语义审查。

## 10. 可重复使用的固定验证流程

以后检查 `Copairing.lean`、`Contraction.lean` 或 Frobenius 文件，可以重复：

1. 运行 `git status --short`、`git diff --stat`、`git diff`；
2. 阅读数学说明、README、模块 docstring；
3. 标出 imports、namespace、section、variables、structures、defs、theorems 和属性；
4. Command + 点击检查 mathlib 依赖；
5. 用 `#check @name` 恢复完整接口；
6. 搜索全部下游使用；
7. 单独编译源文件建立基线；
8. 写只有最小假设的抽象 examples；
9. 为符号、次序和边界写具体实例；
10. 使用公开定理而不是实现展开；
11. 编译源文件、测试文件和直接下游；
12. 运行 `lake test` 和 `lake build`；
13. 搜索 `sorry`、`admit`；
14. 检查所有 warnings；
15. 运行 `git diff --check`；
16. 审查最终 diff 和 Git 状态；
17. 在报告中区分数学结论、编译证据、预先存在的问题和未覆盖范围。

## 11. 审查结论、风险和下一优先级

### 11.1 Findings

- Critical：未发现；
- High：未发现；
- Medium：未发现；
- Low：未发现需要修改源文件的问题。

### 11.2 数学效果

没有修改任何 theorem statement、定义、假设或公共 API。测试只是固定现有行为：

- `toDual x y = form x y`；
- `toDual.toLinearMap = form`；
- 只需交换环、加法交换群和模结构；
- 零模边界成立。

### 11.3 剩余风险

这是对 `PerfectPairing.lean` 及其槽位下游的定向审查，不是对整个 `Linear` 或 `Frobenius` 目录的全面验证。由于所有结构实例都对称，具体数值测试不能独立辨别槽位反转；因此长期保护依赖 theorem statement 和 `Copairing` 下游公式共同完成。

### 11.4 下一优先级

下一项最有数学价值的工作是为 `Copairing.lean` 建立独立测试，重点检查：

- 为什么此处才需要 `Module.Free`、`Module.Finite`；
- `tensorEndEquiv_tmul` 的第一张量腿约定；
- `copairing_contract`；
- `copairing_comm`；
- 基环实例中的 `1 ⊗ 1` 计算。
