/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System.IO;
using System.Collections.Generic;
using System;
using System.Text.RegularExpressions;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        // 将一系列expression作合取
        private Expression ConditionListToExpression(List<Expression> conditions) {
            if(conditions.Count == 0) {
                BoolConstantExpression trueExp = new BoolConstantExpression(true);
                return trueExp;
            }

            Expression exp = conditions[0];
            for (int i = 1; i < conditions.Count; i++) {
                Expression expr = conditions[i];
                exp = new AndExpression(exp, expr);
            }
            return exp;
        }
        
        // 秩函数的终止性验证和后置条件的验证都会走wlp, 但是handleAssert不同, 秩函数只需验证终止性, 不需要关注assert语句, 故处理秩函数时assert语句直接跳过
        private Expression wlp(Statement stmt, Expression postCondition, bool handleAssert) {
            Expression exp = postCondition;
            switch (stmt)
            {
                case VariableAssignStatement varAssign:
                    Expression expression = varAssign.rhs;
                    exp = exp.Substitute(varAssign.variable, expression);
                    break;
                case SubscriptAssignStatement subAssign:
                    var arrayExp = new VariableExpression(subAssign.array);
                    var arrayLenExp = new VariableExpression(subAssign.array.length);
                    ArrayUpdateExpression auexp = new ArrayUpdateExpression(arrayExp, subAssign.subscript, subAssign.rhs, arrayLenExp);
                    exp = exp.Substitute(subAssign.array, auexp);
                    break;
                case AssertStatement assertStmt:
                    if(handleAssert)
                        exp = new AndExpression(exp, assertStmt.pred);
                    break;
                case AssumeStatement assumeStmt:
                    // 加前提
                    ImplicationExpression addConditionExp = new ImplicationExpression(assumeStmt.condition, exp);
                    exp = addConditionExp;
                    break;
                default:
                    break;
            }
            return exp;
        }

        // 从后向前wlp List<Statement>
        private Expression reverseRunStmts(List<Statement> stmts, Expression exp, bool handleAssert) {
            for (int j = stmts.Count -1 ; j >= 0; j--) {
                var stmt = stmts[j];
                if (stmt != null)
                    exp = wlp(stmt, exp, handleAssert);
            }
            return exp;
        }

        // 处理函数调用时的秩函数, 也需要进行参数替换
        private List<Expression> handleFuncRankExps(FunctionCallStatement funcCallStmt) {
            Function callFunc = funcCallStmt.rhs.function;
            // 秩函数处理, 要深拷贝!
            List<Expression> rankExps = new List<Expression>(callFunc.entryLocation.rankingFunctions);
            
            // 秩函数都可能涉及到很多参数，一个个单独处理，需要双层循环
            for(int i = 0; i < rankExps.Count; i++) {
                for(int j = 0; j < callFunc.parameters.Count; j++) {
                    VariableExpression varExp = new VariableExpression(funcCallStmt.rhs.argumentVariables[j]);
                    rankExps[i] = rankExps[i].Substitute(callFunc.parameters[j], varExp);
                }
            }
            return rankExps;
        }

        // 请求函数调用 满足参数要求, 加入后置条件, 即被调函数的requires
        private Expression handleMeetCallRequire(FunctionCallStatement funcCallStmt) {
            Function callFunc = funcCallStmt.rhs.function;
            Expression requireExp = ConditionListToExpression(callFunc.entryLocation.conditions);
            // 把被调函数require用到的变量换了
            for(int i = 0; i < callFunc.parameters.Count; i++) {
                VariableExpression varExp = new VariableExpression(funcCallStmt.rhs.argumentVariables[i]);
                requireExp = requireExp.Substitute(callFunc.parameters[i], varExp);
            }

            return requireExp;
        }

        // 处理函数调用返回，主要处理ensure+返回值
        // 把条件浓缩为一条assume语句处理
        private AssumeStatement handleCallReturnEnsure(FunctionCallStatement funcCallStmt) {
            Function callFunc = funcCallStmt.rhs.function;
            Expression ensureExp = ConditionListToExpression(callFunc.exitLocation.conditions);
            // 1. 把被调函数ensure用到的变量换了 
            for(int i = 0; i < callFunc.parameters.Count; i++) {
                VariableExpression varExp = new VariableExpression(funcCallStmt.rhs.argumentVariables[i]);
                ensureExp = ensureExp.Substitute(callFunc.parameters[i], varExp);
            }

            // 2. 处理返回值
            for(int i = 0; i < callFunc.rvs.Count; i++) {
                VariableExpression varExp = new VariableExpression(funcCallStmt.lhs[i]);
                ensureExp = ensureExp.Substitute(callFunc.rvs[i], varExp);
            }

            // 把一切条件都变成assume语句, 提前变成preExp的话会导致很多问题, 要么有的符号没有处理, 要么把前面语句的信息叠加之后这样加的assume范围不对(不能提前叠加)
            AssumeStatement assumeStmt = new AssumeStatement();
            assumeStmt.condition = ensureExp;

            Console.Write("add assume : \n");
            ensureExp.Print(writer);
            Console.Write("\n");

            return assumeStmt;
        }

        // 最后把重命名的变量名换回来
        private Expression replaceNameBack(Expression rankCmpExp, List<LocalVariable> renamedVarsList) {
            foreach(LocalVariable variable in renamedVarsList) {
                String originName = variable.name;
                originName = Regex.Replace(originName, @"_renamed\d+$", "");
                LocalVariable originNameVar = new LocalVariable 
                {
                    type = variable.type, name = originName
                };
                VariableExpression originNameVarExp = new VariableExpression(originNameVar);
                rankCmpExp = rankCmpExp.Substitute(variable, originNameVarExp);
            }
            return rankCmpExp;
        }

        // 拿到秩函数比较的expression
        private (Expression, List<LocalVariable>) getRankCompareExp(List<Expression> rankExpsBefore, List<Expression> rankExpsAfter) {
            // 不涉及秩函数的返回恒真
            Expression dicDecreaseCmpExp = new BoolConstantExpression(true);
            if(rankExpsBefore.Count == 0 || rankExpsAfter.Count == 0)
                return (dicDecreaseCmpExp, new List<LocalVariable>());

            List<Expression> renamedRankExpsBefore = new List<Expression>();
            // 1. 可能变量会重名了, 重名则无法比较前后区别, 首先需要重命名了
            List<LocalVariable> renamedVarsList = new List<LocalVariable>();
            // 对randExpsBefore进行重命名, 不同元组位置的自由变量可能名字相同, 不能草率重命名!
            // 用一个标号标识
            int freeCnt = 0;
            for(int i = 0; i < rankExpsBefore.Count; i++) {
                Expression renamedRankExp = rankExpsBefore[i];
                HashSet<LocalVariable> freeVars = renamedRankExp.GetFreeVariables();
                foreach(LocalVariable freeVal in freeVars) {
                    // 创建新的自由变量
                    String newName = freeVal.name + "_renamed" + freeCnt;
                    LocalVariable newNameVar = new LocalVariable 
                    {
                        type = freeVal.type, name = newName
                    };
                    renamedVarsList.Add(newNameVar);
                    VariableExpression newNameVarExp = new VariableExpression(newNameVar);
                    renamedRankExp = renamedRankExp.Substitute(freeVal, newNameVarExp);
                }
                renamedRankExpsBefore.Add(renamedRankExp);
            }

            // 2. 构造出比较秩函数字典序的表达式
            // 比如(x, y) < (x1, y1) : (x < x1)或者(x == x1 and y < y1)
            dicDecreaseCmpExp = new BoolConstantExpression(false);
            for(int i = 0; i < renamedRankExpsBefore.Count; i++) {
                Expression rankCompareExp =  new BoolConstantExpression(true);
                // 前i-1个元组都相等, 第i个小于
                for(int j = 0; j < i ; j++)
                    rankCompareExp = new AndExpression(rankCompareExp, new EQExpression(renamedRankExpsBefore[j], rankExpsAfter[j]));
                rankCompareExp = new AndExpression(rankCompareExp, new LTExpression(rankExpsAfter[i], renamedRankExpsBefore[i]));

                dicDecreaseCmpExp = new OrExpression(dicDecreaseCmpExp, rankCompareExp);
            }

            // 3. 保证一下秩函数的非负性
            Expression rankGE = new BoolConstantExpression(true);
            for(int i = 0; i < renamedRankExpsBefore.Count; i++) {
                rankGE = new AndExpression(rankGE, new GEExpression(renamedRankExpsBefore[i], new IntConstantExpression(0)));
                rankGE = new AndExpression(rankGE, new GEExpression(rankExpsAfter[i], new IntConstantExpression(0)));
            }
            dicDecreaseCmpExp = new AndExpression(dicDecreaseCmpExp, rankGE);
            return (dicDecreaseCmpExp, renamedVarsList);
        }

        // 输入前置和后置条件, 调用solver
        private bool getResult(List<Expression> pre, Expression post) {
            ImplicationExpression partFinal = new ImplicationExpression(ConditionListToExpression(pre), post);
            partFinal.Print(writer);
            Console.Write("\n");
            // 具体CheckValid里面已经有取反操作，这里不需要再做
            var partRes = solver.CheckValid(partFinal);
            if(partRes != null) {
                Console.Write("wrong !\n");
                return false;
            }

            Console.Write("right !\n");
            return true;
        }

        private BasicPath deepCopyBasicPath(BasicPath basicPath) {
            BasicPath newPath = new BasicPath();
            newPath.statements = new List<Statement>(basicPath.statements);
            newPath.headConditions = new List<Expression>(basicPath.headConditions);
            newPath.tailConditions = new List<Expression>(basicPath.tailConditions);
            newPath.headRankingFunctions = new List<Expression>(basicPath.headRankingFunctions);
            newPath.tailRankingFunctions = new List<Expression>(basicPath.tailRankingFunctions);
            return newPath;
        }

        // 一个函数一个函数判断
        private int checkOneFunc(Function func) {
            func.Print(writer);
            // 拿到前置条件
            List<Expression> preExpression = func.entryLocation.conditions;
            // 拿到后置条件
            List<Expression> postExpression = func.exitLocation.conditions;
            // 拿到秩函数
            List<Expression> rankingExpressions = func.entryLocation.rankingFunctions;
            // 判断秩函数不能为负
            for(int i = 0; i < rankingExpressions.Count; i++) {
                if(rankingExpressions[i] is NegExpression)
                    return -1;
            }

            // 整体思路:
            // 1. 正向找路径
            // 2. 反向wlp

            Expression exp;
            Queue<(Location, BasicPath, HashSet<int>)> pathList = new Queue<(Location, BasicPath, HashSet<int>)>();
            BasicPath firstPath = new BasicPath();
            firstPath.headConditions = preExpression;
            firstPath.tailConditions = postExpression;
            firstPath.headRankingFunctions = rankingExpressions;
            pathList.Enqueue((func.entryLocation, firstPath, new HashSet<int>()));
            while(pathList.Count > 0) {
                (Location loc, BasicPath curPath, HashSet<int> haveMeetLoopHeads) = pathList.Dequeue();
                Console.Write("travel {0}\n", loc.number);
                List<Statement> stmts = curPath.statements;
                List<Expression> preExp = curPath.headConditions;
                List<Expression> postExp = curPath.tailConditions;
                List<Expression> rankHead = curPath.headRankingFunctions;
                List<Expression> rankTail = curPath.tailRankingFunctions;

                // 判断是否到终点，到终点就路径结束, 开始反向wlp, 否则则继续遍历; 其中循环和函数调用需要分别处理

                // !有可能最后一个stmt也是函数调用, 所以先判断这个, 处理不同, 不然会走入别的分支
                if(stmts.Count > 0 && stmts[stmts.Count-1] is FunctionCallStatement funcCallStmt) {
                    // 要把原来的post换掉，结束当前这个path，在当前基础上加入一个assumeStmt继续走

                    // 取得被调函数的秩函数
                    List<Expression> calleeRankExps = handleFuncRankExps(funcCallStmt);

                    // 1. 参数的约束，换Post, 结束当前path
                    Expression newPost = handleMeetCallRequire(funcCallStmt);
                    List<Statement> newStmts = stmts.GetRange(0, stmts.Count - 1);
                    exp = reverseRunStmts(newStmts, newPost, true);
                    if(!getResult(preExp, exp))
                        return -1;
                    // 秩函数
                    (Expression rankCheckExpFuncCall, List<LocalVariable> renameVarsListFuncCall) = getRankCompareExp(rankHead, calleeRankExps);
                    exp = reverseRunStmts(stmts, rankCheckExpFuncCall, false);
                    exp = replaceNameBack(exp, renameVarsListFuncCall);
                    if(!getResult(preExp, exp))
                        return -1;

                    // 2. 在当前基础上加入一个assumeStmt继续走
                    Statement assumeStmt = handleCallReturnEnsure(funcCallStmt);
                    
                    if(loc.succLocations.Count > 0) {
                        for(int i = 0; i < loc.succLocations.Count; i++) {
                            Location succLoc = loc.succLocations[i];
                            Statement stmt = loc.succStatements[i]!;

                            // 把之前的补上并且加上函数调用结束的assumeStmt
                            List<Statement> beforeStmts = new List<Statement>();
                            // 最后一个调用不处理
                            for(int j = 0; j < stmts.Count - 1; j++) {
                                beforeStmts.Add(stmts[j]);
                            }
                            beforeStmts.Add(assumeStmt);

                            // 加上stmt
                            beforeStmts.Add(stmt);

                            BasicPath newPath = deepCopyBasicPath(curPath);
                            newPath.statements = beforeStmts;
                            pathList.Enqueue((succLoc, newPath, haveMeetLoopHeads));
                        }
                    } else {
                        // 说明它又是函数调用语句又是结尾, 原有的stmts加上assume语句直接处理
                        stmts.Add(assumeStmt);
                        exp = reverseRunStmts(stmts, ConditionListToExpression(postExp), true);
                        if(!getResult(preExp, exp))
                            return -1;
                    }
                } else if(loc is LoopHeadLocation loopLoc) {
                    // fixme 应该没有循环头是结束语句吧
                    // 到函数头了, 取得循环不变式
                    Expression loopInvariants = ConditionListToExpression(loopLoc.invariants);
                    // 取得秩函数
                    List<Expression> loopRankExps = loopLoc.rankingFunctions;

                    // 如果已经不是第一次遍历到这里
                    if(haveMeetLoopHeads.Contains(loc.number)) {
                        // 额外约束二: I && cond -> wp(循环内语句)
                        // 当前路径结束并加入, 由于再一次走到循环点, 后置条件是循环不变式
                        exp = reverseRunStmts(stmts, loopInvariants, true);
                        if(!getResult(preExp, exp))
                            return -1;
                        
                        // 秩函数
                        (Expression rankCheckExpLoop1, List<LocalVariable> renameVarsListLoop1) = getRankCompareExp(rankHead, loopRankExps);
                        exp = reverseRunStmts(stmts, rankCheckExpLoop1, false);
                        exp = replaceNameBack(exp, renameVarsListLoop1);
                        if(!getResult(preExp, exp))
                            return -1;
                        continue;
                    }
                    haveMeetLoopHeads.Add(loc.number);    

                    // 1. 结束当前路径, 后置条件为循环不变式
                    exp = reverseRunStmts(stmts, loopInvariants, true);
                    if(!getResult(preExp, exp))
                        return -1;
                    // 秩函数
                    (Expression rankCheckExpLoop2, List<LocalVariable> renameVarsListLoop2) = getRankCompareExp(rankHead, loopRankExps);
                    exp = reverseRunStmts(stmts, rankCheckExpLoop2, false);
                    exp = replaceNameBack(exp, renameVarsListLoop2);
                    if(!getResult(preExp, exp))
                        return -1;

                    // 2. 开新路径, 前置条件为不变式
                    // 处理过程中会有走出循环的情况, 即处理额外约束一: I && !cond -> 后置条件
                    for(int i = 0; i < loc.succLocations.Count; i++) {
                        Location succLoc = loc.succLocations[i];
                        Statement stmt = loc.succStatements[i]!;

                        List<Statement> newStmts = new List<Statement>();
                        newStmts.Add(stmt);

                        BasicPath newPath = deepCopyBasicPath(curPath);
                        newPath.statements = newStmts;
                        newPath.headConditions = loopLoc.invariants;
                        newPath.headRankingFunctions = loopRankExps;
                        pathList.Enqueue((succLoc, newPath, haveMeetLoopHeads));
                    }

                } else if(loc.succLocations.Count == 0) {
                    // 已经走到最后面了, 可以开始验证了
                    // 先运行整个的stmt, 反向wlp
                    exp = reverseRunStmts(stmts, ConditionListToExpression(postExp), true);
                    if(!getResult(preExp, exp))
                        return -1;
                } else {
                    // 往下走
                    for(int i = 0; i < loc.succLocations.Count; i++) {
                        var succLoc = loc.succLocations[i];
                        Console.Write("add {0}\n", succLoc.number);
                        // 如果直接对List赋值会浅拷贝发生错误
                        List<Statement> newStmts = new List<Statement>(stmts);
                        if(loc.succStatements[i] != null) {
                            var succStmt = loc.succStatements[i]!;
                            if(succStmt is FunctionCallStatement) {
                                Console.Write("it is with loc{0}!\n", succStmt.location);
                            }
                            newStmts.Add(succStmt);
                        }
                        BasicPath newPath = deepCopyBasicPath(curPath);
                        newPath.statements = newStmts;
                        pathList.Enqueue((succLoc, newPath, haveMeetLoopHeads));
                    }
                }
            }
           
            return 1;
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public int Apply(IRMain cfg)
        {
            /// remarks: ACSL语法支持自定义谓词。输入的程序中就可能定义了一些谓词，这里先把他们注册给Solver，后续就不需要特殊的处理
            foreach (Predicate predicate in cfg.predicates)
            {
                solver.definePredicate(predicate);
            }

            // YOUR CODE HERE
            // 根据演绎验证的原理，生成基本路径和验证条件，交由后端Solver求解
            
            // 遍历所有函数
            // -1不成立, 1: 成立, 0: unknown
            foreach (Function f in cfg.functions) {
                int res = checkOneFunc(f);
                // 一旦有unknown的函数就是unknown了
                if(res == 0)    return 0;
                // 一旦有不成立的函数就不成立了
                if(res == -1)   return -1;
            }
            return 1;
        }
    }
}