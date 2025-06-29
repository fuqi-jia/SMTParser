# SMTParser Python绑定

这个目录包含了SMTParser库的Python绑定，允许您从Python代码中使用SMT-LIB2解析和表达式构建功能。

## 功能特性

- **SMT-LIB2文件解析** - 解析标准SMT-LIB2格式文件
- **程序化表达式构建** - 通过API直接构建逻辑表达式
- **多理论支持** - 支持布尔、算术、位向量等多种SMT理论
- **模型求值** - 在给定模型下计算表达式的值
- **优化模理论(OMT)支持** - 支持优化问题
- **高效内存管理** - 使用智能指针进行安全的内存管理

## 系统要求

### 必需依赖
- Python 3.6+
- GMP库 (GNU Multiple Precision Arithmetic Library)
- MPFR库 (GNU Multiple Precision Floating-Point Reliable Library)
- pybind11 (Python绑定框架)

### 安装依赖

#### Ubuntu/Debian
```bash
sudo apt update
sudo apt install -y python3 python3-pip python3-dev
sudo apt install -y libgmp-dev libmpfr-dev
pip3 install pybind11
```

#### Fedora/RHEL/CentOS
```bash
# Fedora
sudo dnf install -y python3 python3-pip python3-devel
sudo dnf install -y gmp-devel mpfr-devel
pip3 install pybind11

# RHEL/CentOS
sudo yum install -y python3 python3-pip python3-devel
sudo yum install -y gmp-devel mpfr-devel
pip3 install pybind11
```

#### macOS
```bash
# 使用Homebrew
brew install python3 gmp mpfr
pip3 install pybind11
```

#### Windows (WSL)
推荐使用WSL (Windows Subsystem for Linux)，然后按照Ubuntu说明安装。

## 构建和安装

### 方法1: 使用构建脚本 (推荐)
```bash
# 从SMTParser根目录运行
chmod +x build_python.sh
./build_python.sh
```

### 方法2: 手动构建
```bash
# 安装Python依赖
pip3 install pybind11 setuptools wheel

# 构建扩展
python3 setup.py build_ext --inplace

# 或安装到系统
python3 setup.py install
```

### 方法3: 使用pip安装
```bash
pip3 install .
```

## 使用示例

### 基本解析示例
```python
import smtparser

# 创建解析器
parser = smtparser.Parser()

# 解析约束字符串
parser.parseStr("(declare-fun x () Int)")
parser.assert_("(assert (> x 0))")

# 获取断言
assertions = parser.getAssertions()
for assertion in assertions:
    print(parser.toString(assertion))
```

### 程序化表达式构建
```python
import smtparser

parser = smtparser.Parser()

# 创建变量
x = parser.mkVarInt("x")
y = parser.mkVarInt("y")

# 构建表达式: (x + y) > 5
sum_expr = parser.mkAdd(x, y)
constraint = parser.mkGt(sum_expr, parser.mkConstInt(5))

print(f"约束: {parser.toString(constraint)}")
```

### 布尔运算
```python
import smtparser

parser = smtparser.Parser()

# 创建布尔变量
p = parser.mkVarBool("p")
q = parser.mkVarBool("q")

# 创建布尔表达式
and_expr = parser.mkAnd(p, q)
or_expr = parser.mkOr(p, q)
not_expr = parser.mkNot(p)
implies_expr = parser.mkImplies(p, q)

print(f"AND: {parser.toString(and_expr)}")
print(f"OR: {parser.toString(or_expr)}")
print(f"NOT: {parser.toString(not_expr)}")
print(f"IMPLIES: {parser.toString(implies_expr)}")
```

### 模型求值
```python
import smtparser

parser = smtparser.Parser()

# 创建变量和表达式
x = parser.mkVarInt("x")
y = parser.mkVarInt("y")
expr = parser.mkAdd(x, y)

# 创建模型
model = smtparser.newModel()
model.add(x, parser.mkConstInt(10))
model.add(y, parser.mkConstInt(20))

# 求值
result = parser.evaluate(expr, model)
print(f"表达式: {parser.toString(expr)}")
print(f"求值结果: {parser.toString(result)}")  # 输出: 30
```

## API参考

### 主要类

#### `Parser`
主要的解析器和表达式构建器类。

**主要方法:**
- `parse(filename)` - 解析SMT-LIB2文件
- `parseStr(constraint)` - 解析约束字符串
- `assert_(constraint)` - 断言约束
- `mkVarInt(name)` - 创建整数变量
- `mkVarBool(name)` - 创建布尔变量
- `mkVarReal(name)` - 创建实数变量
- `mkConstInt(value)` - 创建整数常量
- `mkAdd(expr1, expr2)` - 创建加法表达式
- `mkAnd(expr1, expr2)` - 创建AND表达式
- `toString(expr)` - 将表达式转换为字符串
- `evaluate(expr, model)` - 在模型下求值表达式

#### `DAGNode`
表示表达式的DAG节点。

**主要方法:**
- `getKind()` - 获取节点类型
- `getSort()` - 获取排序(类型)
- `getName()` - 获取名称
- `getChild(index)` - 获取子节点
- `isVar()` - 是否为变量
- `isConst()` - 是否为常量

#### `Model`
表示变量赋值的模型。

**主要方法:**
- `add(var, value)` - 添加变量赋值
- `get(var)` - 获取变量的值
- `size()` - 获取模型大小
- `toString()` - 转换为字符串

### 工厂函数
- `smtparser.newParser()` - 创建新的解析器
- `smtparser.newModel()` - 创建新的模型

### 预定义常量
- `smtparser.BOOL_SORT` - 布尔排序
- `smtparser.INT_SORT` - 整数排序
- `smtparser.REAL_SORT` - 实数排序

## 完整示例

查看`example.py`文件了解更多使用示例。运行示例:

```bash
python3 python_binding/example.py
```

## 故障排除

### 常见问题

**1. 导入错误 "ImportError: No module named 'smtparser'"**
- 确保已成功构建模块
- 检查当前目录下是否有smtparser*.so文件
- 尝试从构建目录运行Python

**2. 构建错误 "gmp.h: No such file or directory"**
- 安装GMP开发包: `sudo apt install libgmp-dev`

**3. 构建错误 "mpfr.h: No such file or directory"**
- 安装MPFR开发包: `sudo apt install libmpfr-dev`

**4. Python版本问题**
- 确保使用Python 3.6或更高版本
- 在一些系统上，可能需要使用`python3`而不是`python`

### 调试构建问题

启用详细构建输出:
```bash
python3 setup.py build_ext --inplace --verbose
```

检查依赖:
```bash
# 检查GMP
find /usr -name "libgmp*" 2>/dev/null

# 检查MPFR
find /usr -name "libmpfr*" 2>/dev/null

# 检查头文件
find /usr -name "gmp.h" 2>/dev/null
find /usr -name "mpfr.h" 2>/dev/null
```

## 性能注意事项

- 使用`smtparser.newParser()`和`smtparser.newModel()`工厂函数以获得更好的内存管理
- 对于大型表达式，考虑重用解析器实例
- Python绑定保持了C++库的高效性，但跨语言调用仍有开销

## 许可证

本Python绑定与SMTParser库采用相同的MIT许可证。

## 支持

如有问题或需要帮助，请查看主项目的GitHub仓库或联系项目维护者。 