我正在考察完全重构这个项目。现在这个项目的结构完全是为了对应Chen-Jeannin的文章Harder-Narasimhan Game而组织的。但从Lean的工程实践角度来看这种组织并不很好。我预期的重构路线如下：
1. 每个模块不再区分Results.lean和Impl.lean。现在我们不追求Results.lean中函数的签名和文章中的结论精确匹配，而是使得该理论中重要的，被使用的结论暴露出来，其中也包括Impl.lean中那些被广泛使用的函数。当然，有些只作为中间步骤的函数可以不暴露出来。
2. 模块化设计组织，仿照Mathlib。我的想法是：本项目分为4个文件夹：
(2a) `PayoffFunction`: 其中Defs.lean定义\mu,\mu_min,\mu_max,...等。然后下设若干个文件或者文件夹讨论它不同的条件及性质。如，现在的semistability就是一个单独的文件（外加一个可能相关的文件夹）。我可能说得不是很清楚，但总体思路就是仿照Mathlib的组织结构
(2b) `Filtration`: 定义并陈述Harder-Narasimhan Filtration的相关结论（存在性，唯一性，等）
(2c) `JordanHolder`: 定义并陈述Jordan-Hölder Filtration的相关结论
(2d) `Coprimary`: 定义并陈述Coprimary Filtration的相关结论
3. 重新组织命名空间。需要使用scpoe和section variables
4. 现在的payoff function是一个裸的定义`μ : Intvl ℒ → S`。它最好做成一个def或一个structure `PayoffFunction`。然后我们**必须**充分利用dot notation。如，μmax应该变成μ.max，然后现在的Semistable应该变成μ.isSemistable（我不确定大小写，请参考mathlib命名规则）。此外，现在的Resμ也应该变成μ.restriction。其余定义类似。而现在的HarderNarasimhanFiltration应该变成μ.HarderNarasimhanFiltration。ConvexI之类的概念如何变我还没想好，你可以想一下。
5. 你需要覆盖到这个项目的方方面面，不要遗漏。
6. docstring需要重写。变量等的命名以及代码formatting参考如下链接：

https://leanprover-community.github.io/contribute/style.html
https://leanprover-community.github.io/contribute/doc.html
https://leanprover-community.github.io/contribute/naming.html

请先不要动代码，扫描整个项目，仔细思考以后生成一份详尽的重构计划书给我过目。计划书要固化保存于一个markdown文件中。其中要包括代码如何组织，结构定义如何设计，等方方面面。等我过目我们讨论修改完了再动手。