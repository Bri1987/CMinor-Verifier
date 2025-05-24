# 报告

## 1 实现过程

首先将验证过程分为多个函数的验证，遍历所有函数分别验证，一旦有函数未通过验证，则直接返回UNVERIFIED。

对每个函数的验证过程在`int checkOneFunc(Function func)`函数中，接下来主要说明该函数的代码思路。



### 1.1 前置准备与整体思路

前置准备：

拿到函数的前置条件、后置条件和秩函数，并判断秩函数不是负值。



对于每个函数而言，整体验证思路是：

1. 正向遍历搜索到完整的基本路径
2. 对每条基本路径收集到的Statements反向遍历执行wlp，不断求最弱前置条件，结合前置后置条件和秩函数等信息生成表达式验证



### 1.2 部分正确性检验

即验证$\varphi \rightarrow wp(st_1;st_2;...;st_n, \psi)$是有效式

#### 1.2.1 正向遍历搜索到完整的基本路径

整体采用BFS（其实后面感觉DFS会更好），队列中的每个元素为（当前处理到的Location，BasicPath，记录处理过的LoopHeadLocation的标号）的元组。

其中对每条基本路径处理过的LoopHeadLocation标号的记录为了方便后续对循环的处理，第一次进入循环与非首次进入循环的处理不同。



具体不断向后搜索时对语句的处理分为以下四种情况：

##### 函数调用

- 结束当前基本路径的收集，并读取被调函数的前置条件，将形参替换为该条函数调用语句的实参（`handleMeetCallRequire`中实现），将替换后得到的表达式作为当前基本路径的后置条件。
- 得到一条新基本路径继续搜索。
  - 首先得到被调函数的后置条件，将形参替换为该条函数调用语句的实参并替换返回值（`handleCallReturnEnsure`中实现），将替换后得到的表达式作为一条新的AssumeStatement的conditon
  - 新的基本路径首先集成原先基本路径的所有语句，再添加新得到的AssumeStatement
  - 遍历当前Location的所有succLocations，分别加入该新的基本路径，放入工作表（如果没有succLocations了，也要将加入AssumeStatement的新基本路径进行收集）。

##### 循环

- 第一次进入循环：

  - 结束当前基本路径的收集，将当前基本路径的后置条件设置为该循环的循环不变式
  - 得到一条新基本路径继续搜索，该基本路径的前置条件为循环不变式，语句序列先置空，再遍历当前Location的所有succLocations，分别加入该新的基本路径，放入工作表。在处理过程中会有走出循环的情况，即处理了额外约束一： $I \and \neg p \rightarrow \psi$

- 非首次进入循环：

  结束当前基本路径的收集，将当前基本路径的后置条件设置为该循环的循环不变式。在处理过程中由于再次回到循环头，能处理额外约束二：$I \and p\rightarrow wp(st, I)$

##### 搜索到EXIT_LOC

即该条基本路径结束。

##### 未搜索到EXIT_LOC并且当前处理普通语句

遍历当前Location的所有succLocations，分别加入当前基本路径，放入工作表。



#### 1.2.2 对基本路径收集到的Statements反向遍历执行wlp

对收集到的基本路径从后向前不断求最弱前置条件，主要在函数`Expression reverseRunStmts(List<Statement> stmts, Expression exp, bool handleAssert)`和`Expression wlp(Statement stmt, Expression postCondition, bool handleAssert)`进行实现，主要处理的Statement类别有以下几种：

- VariableAssignStatement：即实现$w p(x:=e, \psi)=\psi[x \mapsto e]$，调用SubStitute方法对变量进行替换
- SubscriptAssignStatement：即实现$w p(a[e_1]:=e_2, \psi)=\psi[a \mapsto a<e_1 \lhd e_2>]$，调用数组的SubStitute方法对变量进行替换
- AssertStatement：即实现$w p(\text { assert } p, \psi)=p \wedge \psi$，将assert的内容和输入的后置表达式进行与操作
- AssumeStatement：即实现$w p(\text { assume } p, \psi)=p \rightarrow \psi$。使用一个新的蕴涵表达式，将assme的内容作为蕴涵表达式的前件，输入的后置表达式作为后件

其中函数调用语句在收集基本路径时就进行了处理，不会被添加到要处理的List<Statements>中



### 1.3 终止性检验

在处理函数调用和循环时需进行终止性检验，即检验$\varphi \rightarrow wlp(st_1;st_2;...;st_n, \delta(x) \prec \delta(x'))[x'\mapsto x]$

#### 1.3.1 整体思路

主要在函数`(Expression, List<LocalVariable>) getRankCompareExp(List<Expression> rankExpsBefore, List<Expression> rankExpsAfter)`和`Expression replaceNameBack(Expression rankCmpExp, List<LocalVariable> renamedVarsList)`中进行实现，输入两个秩函数，得到能检验秩函数良基关系和非负性的表达式，并在该表达式进行wlp之后将重命名的变量改回原名。

1. 对于前面的秩函数进行变量重命名
2. 构造出比较秩函数元组字典序大小的表达式：比如对于秩函数比较(x, y) < (x1, y1) ，构造$(x < x1)\or(x = x1 \and y < y1)$
3. 保证两个秩函数的非负性。结合2和3的约束得到能检验秩函数良基关系和非负性的表达式
4. 结合收集的基本路径，对上一步得到的表达式进行wlp。wlp方式与之前基本相同，与部分正确性检验的wlp不同的是，该表达式目的只是验证终止性，不需要处理AssertStatement。
5. 将被重命名的变量改回原名



#### 1.3.2 函数调用相关处理

1. 将被调用函数的秩函数中的形参替换为当前函数的实参，在`handleFuncRankExps`实现。
2. 比较秩函数间的良基关系：被调函数的秩函数 $\prec$ 当前路径头的秩函数



#### 1.3.3 循环相关处理

每次遍历到循环头，比较秩函数间的良基关系：循环的秩函数 $\prec$ 当前路径头的秩函数

## 2 过程中遇到的问题以及解决方式

1. 之前跑QuickSort-soln测例中发现生成的表达式中缺少最后一个函数调用应生成的assume内容
   - 问题：最初在搜索收集完整基本路径时，先判断了是否搜索到EXIT_LOC，如果搜索到就直接结束了，没有搜索到EXIT_LOC才继续判断是不是遇到函数调用/循环头等特殊语句。这样没有考虑到有的时候走到EXIT_LOC的Statement边也可能是函数调用语句，导致提前判定该基本路径结束，缺少最后的assume内容
   - 解决方式：将是否搜索到EXIT_LOC的判断挪后，先判断当前收集到的最后一条语句是否为函数调用，如果执行完函数调用语句走到了EXIT_LOC，即使没有succLocations了，也要将加入AssumeStatement的新基本路径进行收集处理。
2. 秩函数wlp运行结果出错
   - 问题：终止性检验和部分正确性检验使用的是同一个wlp函数，但终止性检验的秩函数在做wlp时不需要处理assert语句，最开始没有反应过这个问题
   - 解决方式：在wlp函数中增加一个布尔变量代表是终止性检验或部分正确性检验，如果是正在做终止性检验，即跳过所有assert语句的处理
3. C#的深拷贝与浅拷贝的问题
   - 问题：由于搜索完整基本路径时需要不断遍历当前Location的所有succLocations，分别加入基本路径，所以需要很多List<T>的赋值操作，但是C#默认的 List<T>都是浅拷贝的，可能在不经意间对一个List<T>的操作影响了其他的List<T>；包括在秩函数形参到实参的替换时，List<T>的参数传递也是浅拷贝，出现过因为想得到一个实参替换后的秩函数，不小心影响修改了本身的秩函数，导致后续再次使用该秩函数时处理错误的问题，最初没有考虑到这个问题
   - 解决方式：在必要的时候使用深拷贝