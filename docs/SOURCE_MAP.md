# 源码地图

- `LiuWang/Target.lean`：精确主命题的定义，不是证明。
- `LiuWang/Core.lean`、`LiuWang/Community.lean`、`LiuWang/Foundations/`：复用基础与兼容移植。
- `LiuWang/Proof/SourceRoute/`：按原论文结构组织的证明组件；条件与未付项保留在实际定理类型中。
- `LiuWang/Proof/SourceRoute/LowSum/Continuation/Restart/OriginalV1/CountCap/Counts.lean`：条件性实际四零计数上界。
- `LiuWang/Proof/SourceRoute/HighSum/Continuation/Payment/Checked/Restart/OriginalV1/HeightCases/Payment.lean`：逐高度分类下的条件性有限 K3。
- `LiuWang/Proof/SourceRoute/SecondArc/Continuation/ArithmeticPayment/CountPayment/Restart/OriginalV1/LowHeight/Assembly.lean`：含尚未支付低标量的 M1 合账。
- `MathlibNt/`、`AnalyticNumberTheory/`、`PrimeNumberTheoremAnd/`、`BombieriVinogradov/`、`Robin1984/`：选定的复用证明库及其来源适配。
- `Examples/`：基础组件消费者示例，不是无条件主定理演示。

`LiuWang.lean` 是联合导入入口。目录中也保留较早的证明组件；目录存在、模块导入和数学依赖全部消除是三种不同状态。
