# 弱 3-随机性与 Luzin (N)

Lean 4 项目形式化了论文的主定理、Cantor 空间定位定理、引理 2.2–4.2 和引理 5.2 的延拓。引理 5.1 已有拓扑同胚、有效区间编码与测度缩放的证明；从实数快速名字计算逆地址前缀的结论尚未单列。

- [Weak_3_Randomness_and_Luzin_N.lean](Weak_3_Randomness_and_Luzin_N.lean) 汇总模块与原文的对应关系。
- [Weak_3_Randomness_and_Luzin_N/GuoMain.lean](Weak_3_Randomness_and_Luzin_N/GuoMain.lean) 包含主定理与 Luzin (N) 反例。
- [Axioms.lean](Axioms.lean) 统一检查主要定理的公理依赖。
- [docs](docs) 保存构建与公理核验记录。

工具链为 Lean 4.32.2，mathlib 版本为 v4.32.2。在本目录运行：

```powershell
lake build -Kjobs=4
lake env lean Axioms.lean
```

论文：[PDF](paper/Weak_3_Randomness_and_Luzin_N.pdf) · [TeX 源稿](paper/Weak_3_Randomness_and_Luzin_N.tex)
