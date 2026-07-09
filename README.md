1. This repository contains the source codes of the paper entitled "A Neuro-Symbolic Pipeline for Automated Synthesis and Verification of OCL Constraints".

    Abstract: Authoring OCL constraints manually in Model-Driven Engineering is error-prone. While Large Language Models offer a potential solution for automated synthesis, they suffer from structural and semantic hallucinations. Current LLM-based approaches primarily target statistical translation accuracy, lacking formal guarantees of semantic correctness. We propose a neuro-symbolic synthesis pipeline that couples LLM generation with a three-layered defense mechanism and a self-correction loop. Layer 1 enforces structural compliance via JSON Schema validation, and Layer 2 performs static type checking within the UML context. Crucially, Layer 3 translates the candidate OCL constraint into SMT formulas for strict semantic equivalence checking with the reference specification. To ensure decidability, we define a decidable OCL subset and introduce a novel bounded SMT encoding strategy. This strategy employs a value-condition separation mechanism to handle OCL's four-valued logic and abstracts collection algebra into counting functions with bounded quantifier elimination, reducing complex constraints to quantifier-free formulas. Evaluation on a benchmark of 137 OCL constraints demonstrates that the pipeline achieves a strict semantic equivalence rate of 98.54\%, while maintaining computational tractability within standard bounded scopes.

2. Run main.py to get started. To disable specific components, instantiate the AblationSwitch class with a predefined preset (e.g., exp1_pre_verification) or custom overrides, and pass it to the main() function. A brief introduction of each file:

    (1) main.py: The core execution script. It orchestrates the translation of natural language requirements into OCL ASTs using an LLM and implements a multi-layer checking pipeline comprising structural, semantic, and formal verification.

    (2) config.py: Defines global configurations, including LLM parameters, and implements the AblationSwitch class to enable or disable specific checking layers and experimental presets.

    (3) utils.py: Provides utility functions for interacting with the LLM API, including structured response generation and transient error retry mechanisms.

    (4) json_schema.py: Defines the Pydantic models representing the OCL AST structure, serving as the schema constraint for Layer 1 structural validation.

    (5) semantic_checker.py: Implements the Layer 2 static type checker. It resolves UML structural contexts, constructs type environments, and enforces strict type checking and null-safety rules on the generated OCL AST.

    (6) Z3_verification.py: Implements the Layer 3 formal verification. It translates UML class diagrams and OCL constraints into Z3 formulas and performs bounded equivalence checking between LLM generated and reference OCL ASTs.

    (7) benchmark.json: The evaluation dataset comprising 32 UML models with 137 natural language requirements and their corresponding reference OCL constraints.

    (8) benchmark_consistency_check.py: A verification script that uses the Z3 encoder to verify the structural consistency and satisfiability of the reference OCL constraints within the provided benchmark UML models.

    (9) benchmark_consistency_report.json: The output artifact from the consistency checker, documenting the satisfiability status and witness states for each benchmark case.

3. Source information of benchmark cases:

    (1) The following cases are adapted from established industrial benchmarks and academic educational models within the Model-Driven Engineering community, designed to evaluate constraint synthesis under foundational and intermediate structural complexity:

    Royal & Loyal (case_06): Adapted from the industrial benchmark model originally introduced by Warmer and Kleppe. The constraints evaluate basic navigation, attribute domain restrictions, and conditional logic over associations.

    Company, Department, and Employee Systems (case_01, case_04, case_09): Derived from widely utilized company management models prevalent in OCL verification literature, such as the works of Cabot et al. and the USE tool test suites. These cases cover foundational attribute checks, collection algebraic operations such as sum aggregation, and self-referential association navigation.

    Library Systems (case_13, case_27): Adapted from standard library management educational models. The constraints validate collection size limits, conditional state transitions, and arithmetic calculations for fines.

    University Course Registration (case_25): Adapted from the classic university enrollment system frequently referenced in OCL validation studies. The constraints verify complex collection operations, specifically the application of includesAll for prerequisite course verification and conditional GPA restrictions.

    Standard Abstract Data Types and Domain Models (case_02, case_03, case_05, case_07, case_08, case_10, case_11, case_12, case_14, case_15): Adapted from canonical abstract data types and domain-specific educational examples. These cases test basic arithmetic operators, null-safe navigation for optional associations, collection intersection operations, multi-variable iterators for geometric calculations, and uniqueness constraints for problem domains like Sudoku and cinema seating.

    (2) The following cases are manually designed for complex, domain-specific business scenarios. These scenarios are intended to evaluate constraint synthesis under realistic operational logic and to cover diverse language constructs within the decidable OCL subset:

    Smart Climate Control System (case_16): Tests cross-object property navigation, absolute value operations, and complex logical implications.

    IoT Security & Access Hub (case_17): Evaluates nested collection iterators, multi-level association navigation, and security state constraints.

    Smart Microgrid Manager (case_18): Verifies real-domain arithmetic, collection summation, and system state linkage constraints.

    International Freight & Container Tracking (case_19): Tests weight aggregation calculations, multi-condition state evaluation, and date logic.

    Multi-Warehouse Inventory Management (case_20): Evaluates inventory calculations, state enumeration set inclusion, and cross-entity property constraints.

    E-Commerce Marketplace Order Processing (case_21): Verifies complex collect iterators, conditional shipping logic, and anti-self-purchase navigation constraints.

    Hospital Ward Bed Management (case_22): Tests let-in expressions, reject iterators, and complex cross-contamination prevention logic.

    Prescription & Drug Interaction System (case_23): Evaluates excludesAll operations, nested select and collect iterators, and allergic drug exclusion logic.

    Medical Device Telemetry & Alerts (case_24): Verifies multi-variable forAll uniqueness constraints and the relationship between device active status and data streams.

    Online Exam & Proctoring System (case_26): Tests exam duration arithmetic, suspicious event counting, and concurrent session limitations.

    Peer-to-Peer (P2P) Lending Platform (case_28): Evaluates credit score navigation, debt-to-income ratio arithmetic, and anti-self-funding constraints.

    Crypto Exchange & Wallet System (case_29): Verifies asset non-negativity constraints, sanction state freezing logic, and transaction ownership consistency.

    Credit Card Risk Engine (case_30): Tests the application of let-in expressions in pending amount calculations and cross-border transaction risk control constraints.

    Insurance Claim Processing System (case_31): Evaluates the application of if-then-else expressions in claim payout calculations and coverage ratio constraints.

    Education Assessment System (case_32): Verifies the application of collection literals in enumeration validation and includesAll and asSet operations across nested collections.