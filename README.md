OCL2Z3: 基于 LLM 反射机制与形式化验证的 OCL 约束自动生成与评估系统
🎯 项目概览
本系统旨在解决自然语言到 OCL 约束的自动翻译问题。针对 LLM 在生成 OCL 时频发的“语法幻觉”与“逻辑幻觉”（如集合/标量混用、空导航崩溃、未绑定变量等），系统构建了一个“生成-校验-修复”的闭环流水线，并结合 Z3 定理证明器，提出了一种基于语义体积采样的定量等价性评估方法，突破了传统定性评估的局限。

🏗️ 核心架构与工作流
系统采用三层防御架构与闭环反射机制：


NL Requirement
     
     

 1. LLM Structured Generation (LLM + Pydantic Schema)    
    - 强制 JSON Schema 约束解码                             
    - Discriminated Union 保证 AST 节点类型正确
                      
                      
 2. 三层防线校验                                          
    🛡️ Layer 1: Pydantic 深度校验 (结构拦截)               
    🛡️ Layer 2: Semantic Firewall (语义拦截)             
       - 类型推导与交叉校验 (防 declared_type 幻觉)          
       - 集合/标量维度坍塌检查 (防 self.staff->salary 错误)  
       - OCL 三值逻辑下的安全传播验证                        
    🛡️ Layer 3: Z3 可编译性检查 (编译拦截)                  
       - Sort Mismatch 提前拦截                           
                       (若拦截失败，携带精准 Error 反馈给 LLM 重试)
                      

 3. Z3 语义体积采样与评分            
   - 有界元模型编码                         
   - 弱化偏差 x & 强化偏差 y 计算                          
   - 非对称非线性平滑打分: 100 * max(0, 1 - α(x/M) - β(y/M)²) 

代码文件介绍
1. utils.py
作用：基础设施层。封装 LLM API 调用逻辑，提供带有弹性容错的结构化解码接口。
代码骨架：
瞬态错误判定常量与逻辑（TRANSIENT_ERROR_CODES 等）。
clean_code_block()：Markdown 格式剥离器。
call_llm_structured()：LLM 调用核心包装器。
核心实现：
将 Pydantic 的 model_json_schema() 强制注入到 System Instruction 中，配合 response_mime_type="application/json" 触发 LLM 的原生 JSON 输出模式。实现了工业级的指数退避重试机制，对 429/5xx 等瞬态 API 错误进行带有抖动因子的自动重试，确保批量基准测试的鲁棒性。

2. config.py
作用：全局配置中心。管理 LLM 后端选择与生成超参数。
代码骨架：
CURRENT_MODEL：当前调用的 LLM 模型标识。
TEMPERATURE：LLM 采样温度。
MAX_RETRIES：自愈合最大重试次数。
核心实现：
通过环境变量读取LLM后端，核心设定在于将 TEMPERATURE 硬编码为 0.0，这是形式化代码生成的必要条件，旨在抑制 LLM 的统计随机性，最大化 AST 生成的确定性与逻辑正确率。

3. json_schema.py
作用：OCL AST 的规范数据模型。基于 Pydantic 定义严格的树状结构，同时作为 LLM 结构化解码的 Schema 约束。
代码骨架：
OCLNode：所有 AST 节点的基类。
具体节点定义：LiteralExpression、PropertyCall、IteratorExpression 等 12 种标准 OCL 构造。
OCLExpression：使用 Annotated 和判别器标签的多态联合类型。
OCLDocument：完整的 OCL 文档根模型。
核心实现：
利用 Pydantic V2 的 Field(discriminator="type") 实现严格的判别联合，强制 LLM 输出的 JSON 在反序列化时必须匹配精确的节点类型。通过 TypeLiteral 限制了操作符（如 +, ->, implies）和迭代器类型的枚举范围，从根本上杜绝了 LLM 生成非法 OCL 语法的可能性。

4. semantic_firewall.py
作用：AST 预校验层。在 Z3 编码前执行严格的 OCL 类型推导与 UML 元模型合规性检查，拦截结构性与类型级幻觉。
代码骨架：
MetamodelRegistry：静态元模型库，解析 UML 上下文。
TypeEnvironment：动态符号表，维护迭代器与局部变量的作用域栈。
OCLSemanticChecker：基于访问者模式的核心校验引擎。
核心实现：
通过递归推导 AST 节点的返回类型，实施严格的维度与类型守卫。核心逻辑包括：集合与标量的维度坍塌拦截（如对集合使用算术运算符）、OCL 箭头与点号语法的多重度校验（Set 必须用 ->，[1..1] 必须用 .）、以及 Null Safety 的静态推断。所有违规均抛出带有精确上下文的 SemanticError，为 LLM 自愈合提供可操作的反馈。

5. Z3_verification.py
作用：形式化验证后端。将 OCL AST 编码为 SMT-LIB 公理，并基于蕴含关系判定 LLM 生成约束与 Ground Truth 的逻辑等价性。
代码骨架：
BoundedMetamodelEncoder：有限域元模型编码器，将 UML 类图映射为 Z3 数据类型和全局公理。
OCLZ3Translator：AST 到 Z3 表达式的翻译器。
check_equivalence()：基于蕴含关系的定性分级判定函数。
check_z3_translatable()：Z3 编译沙箱预检。
核心实现：
采用有界模型检验（BMC）思想，通过 scope=3 限定实例域。翻译器核心维护了 CollectionRef 标记类，将 OCL 的隐式 collect 和集合导航严密映射为基于计数的 Z3 函数组合。验证逻辑摒弃了不可靠的模型计数，直接求解两个蕴含关系（GT => LLM 和 LLM => GT）的 SAT 性，将结果严格划分为 EQUIVALENT、STRENGTHENED、WEAKENED 和 INCOMPARABLE 四个逻辑偏序等级，消除了无界属性域导致的枚举发散问题。

6. mainmain.py
作用：系统主控流水线。负责驱动端到端的 OCL 约束生成、多级校验自愈合以及等价性评估流程。
代码骨架：
SYSTEM_INSTRUCTION：对 LLM 的强约束系统指令，定义 OCL AST 的生成规范。
build_dynamic_prompt()：基于 UML 元模型和自然语言需求动态构造 Few-Shot Prompt。
generate_ast_with_reflexion()：带反馈闭环的 LLM 生成核心循环。
main()：批量数据驱动的主入口，遍历基准测试用例并调度生成与评估。
核心实现：
实现了三级防线的“自愈合”生成机制。LLM 生成的 AST 依次经过 Pydantic Schema 校验（语法层）、Semantic Firewall 校验（类型系统层）和 Z3 Translatable 校验（形式化编译层）。任何一级抛出异常，异常信息将作为精确的 System Feedback 拼接到上下文中，触发 LLM 重新生成，直至生成合法 AST 或达到最大重试次数。评估阶段调用 evaluate_constraint 获取离散的语义等价性分级。

7. benchmark_v5.json
作用：标准评估数据集。提供多领域、多复杂度的 UML 元模型与 Ground Truth OCL 约束。


🌟 核心优势与创新点
1.形式化验证驱动的闭环反射机制

突破了传统 LLM 单次生成或简单自我反思的范式。系统将形式化工具（语义防火墙与 Z3 编译器）作为“确定性裁判”，对 LLM 的输出进行严苛校验。一旦发现逻辑错误，将结构化的形式化报错（而非模糊的自然语言评价）反馈给 LLM，实现了“生成-验证-反馈-修正”的工程闭环，极大提升了复杂 OCL 约束的生成成功率。

2.超越语法约束的深度语义防火墙

常规方法仅依赖 JSON Schema 约束 AST 的结构，无法拦截“合法但无意义”的逻辑幻觉（如在集合上调用点语法、访问不存在的属性）。本系统引入了基于 UML 元模型的动态符号表与类型推导引擎，在翻译至 Z3 之前，提前阻断维度坍塌、类型违例与未绑定变量等深层语义错误，大幅降低了后续形式化验证的崩溃率。

3.基于语义体积采样的定量等价性评估

传统评估多采用字符串匹配或 AST 结构比对，无法识别“逻辑等价但写法不同”的 OCL 表达式（如 size > 0 与 notEmpty）。本系统将 OCL 约束编译为一阶逻辑公式，通过 Z3 求解器枚举反例模型空间，计算 Ground Truth 与 LLM 输出之间的语义体积偏差，实现了对“部分正确”约束的细粒度连续评分。

4.面向 OCL 规范的 Null Safety 编码

OCL 的三值逻辑是自动翻译的痛点，null 导航极易导致形式化工具崩溃或误判。系统在 Z3 编码层完整实现了安全条件的动态传播机制，确保了 invalid/null 状态在逻辑算子中的短路行为符合 OCL 标准，提升了形式化验证的鲁棒性。


⚠️ 当前劣势与已知局限

1.有限个体域验证的内在妥协

受限于 Z3 求解器的能力，元模型编码采用固定 Scope（如默认 3 个实例）的小范围边界。这意味着系统只能保证“在有限规模内”的等价性验证。若反例需要 4 个以上的对象交互才能触发（如复杂的互斥或分配问题），系统将无法捕获，存在漏报风险。

2.复杂约束下的状态空间爆炸

对于包含多重迭代变量（如 forAll(p1, p2, p3 | ...)）或深层嵌套 collect/select 的复杂约束，Z3 翻译会产生笛卡尔积式的表达式膨胀，极易导致求解器超时，无法给出评分。系统的评估能力受制于约束的逻辑深度。

3.依赖 LLM 推理上限与高延迟成本

系统的最终上限受制于底层 LLM 的逻辑推理能力。对于涉及多重否定、复杂时间序列或多跳间接关联的 NL 需求，LLM 往往难以理解，即使提供多次反射机会仍可能无法产出合法 AST。同时，多轮反射机制导致 Token 消耗大、运行延迟高，难以支撑超大规模的实时生成。

4.UML 上下文注入的上下文窗口瓶颈

当前系统完全依赖 Prompt 注入 UML 元模型。当面对包含数十个类与复杂关联的大型工业级模型时，元模型文本将超出 LLM 的有效上下文窗口，导致 LLM 出现严重的遗忘和幻觉，系统尚未引入 RAG 等检索增强机制来应对超大模型。