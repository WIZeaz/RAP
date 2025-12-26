<instruction>
你正在对ArceOS进行安全审计，以文件为单位，寻找文件中每个函数中是否存在潜在的安全漏洞。你需要为这些漏洞编写安全审计报告，这份安全审计报告将由专业的安全审计人员进行进一步处理。你需要寻找的安全漏洞包括并不限于：

- 内存安全问题 (use-after-free, double-free, dangling pointer等)
- 内存泄漏问题
- 多线程下的race condition
- OS相关缺陷（死锁，违反标准定义的行为）
- 函数逻辑缺陷（不符合API标准，意料之外的panic等）

你需要审计的文件放在`<audit></audit>`标签之间。

在`<context></context>`之间提供了和审计文件相关的其他项目源文件，提供上下文信息。不需要对这些文件进行安全审计。
</instruction>

<output-format>
你需要按照格式生成markdown格式的安全审计报告。安全审计报告需要遵循markdown格式，分为几个部分：
1. 审计的文件名。输出文件在项目中的相对路径。
2. 输出发现的每个bug。每个bug包含以下部分:
	1. bug所在的函数名。
	2. bug分类。按以下进行分类: `01-涉及unsafe代码的安全缺陷`, `02-死锁类缺陷`, `03-内存泄漏`, `04-Panic和逻辑错误`。不要使用任何其他分类标签。
	3. 详细bug描述。描述该bug的具体细节。
	4. bug复现方式。报告如何复现该bug，或bug发生的条件。如果能使用unittest复现，提供相应PoC。
你的输出应该只应该包含安全审计报告，不包含任何其他内容。
`<example></example>`中包含了供参考的安全审计模板
</output-format>

<example>
- 审计文件：`src/lib.rs`

# bug-1
- **函数名**: `foo`
- **bug分类**: `01-涉及unsafe代码的安全缺陷`
- **详细bug描述**: 
(详细描述bug)
- **bug复现方式**: 
(描述如何复现bug)
（如果有PoC，提供PoC代码）:
```rust
// ...
```

# bug-2
（按以上格式输出）
</example>

<context>
{{context}}
</context>

<audit>
文件在项目中的相对路径: {{relative_path}}

文件的内容:

```rust
{{content}}
```
</audit>

