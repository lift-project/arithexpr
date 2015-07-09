package apart
package tools

import java.io._

import apart.arithmetic._

object ExprPrinter {
  def dump(expr: ArithExpr, depth: Int = 0): Unit = {
    if(depth == 0)
      println("[***] Expression dump")

    print("  |" * depth + "- ")

    expr match {
      case ArithExprFunction(_,f) =>
        println(s"fct")
        dump(f.min,depth+1)
        dump(f.max,depth+1)
      case Cst(e) =>
        println(s"$e")
      case Var(a,b) =>
        println(s"var $a")
        dump(b.min,depth+1)
        dump(b.max,depth+1)
      case Pow(base, exp) =>
        println("Pow")
        dump(base,depth+1)
        dump(exp,depth+1)
      case Log(b,x) =>
        println("Log")
        dump(b,depth+1)
        dump(x,depth+1)
      case Mod(dividend, divisor) =>
        println("Mod")
        dump(dividend,depth+1)
        dump(divisor,depth+1)
      case Prod(factors) =>
        println("Prod")
        factors.map(dump(_, depth+1))
      case Sum(terms) =>
        println("Sum")
        terms.map(dump(_, depth+1))
      case IntDiv(n, d) =>
        println("IntDiv")
        dump(n,depth+1)
        dump(d,depth+1)

      case IfThenElse(i,t,e) =>
        println("if")
        dump(i.lhs,depth+1)
        println("  |" * (depth+1) + s"- ${i.op}")
        dump(i.rhs,depth+1)
        println("  |" * depth + "- then")
        dump(t,depth+1)
        println("  |" * depth + "- else")
        dump(e,depth+1)
      case ? =>
        println("?")
      case _ =>
        println(s"[***] UNKNOWN $expr")
    }
  }


  class DotNode(label: String, shape: String = "oval", color: String = "\"#eee8d5\""){
    val id: Int = { DotGraph.dotcounter = DotGraph.dotcounter+1; DotGraph.dotcounter}

    override def toString: String = {
      id.toString + "  [label=\"" + label + "\", style=filled, fillcolor="+color+", shape="+shape+"];"
    }
  }


  class DotGraph(subgraph: Boolean = false, label: String = "graph") extends DotNode(label) {
    val gid: Int = { DotGraph.clusters = DotGraph.clusters+1; DotGraph.clusters}

    var nodes: List[DotNode] = List[DotNode]()
    var edges: List[(Int, Int)] = List[(Int, Int)]()

    def addNode(label: String, shape: String = "oval", color: String = "\"#eee8d5\""): DotNode = {
      val node = new DotNode(label,shape,color)
      nodes = nodes :+ node
      node
    }

    def addNode(node: DotNode): DotNode = {
      nodes = nodes :+ node
      node
    }

    def addEdge(from: Int, to: Int) = {
      edges = (from,to) :: edges
    }

    def isSubgraph = subgraph

    override def toString(): String = {
      var str =
        if (!subgraph)
          """digraph G {
            |  graph [ranksep=0.5];
            |""".stripMargin
        else
          s"subgraph cluster_$gid {\n  label=" + "\"" + label + "\";\n"

      nodes.foreach(n => str += s"  $n\n")
      edges.foreach(e => str += s"  ${e._1} -> ${e._2};\n")

      str += "}"
      str
    }
  }
  object DotGraph {
    var dotcounter = 0
    var nodecounter = 0
    var clusters = 0
  }

  def dot(expr: ArithExpr, graph: DotGraph = new DotGraph(), parent: Int = -1): Int = {
    val hash = Integer.toHexString(expr.digest())
    def patch(label: String) = label + "\\n" + hash

    // Build current node
    val node: DotNode = expr match {
      case ArithExprFunction(_, f) =>
        graph.addNode(f.toString)
      case Cst(e) =>
        graph.addNode(e.toString, color = "\"#268bd2\"")
      case Var(a, b) =>
        graph.addNode(s"{$a|{${expr.min}|${expr.max}}}", shape = "record", color = "\"#b58900\"")
      case Pow(base, exp) =>
        graph.addNode(s"{Pow|{${expr.min}|${expr.max}}}", shape = "record")
      case Log(b, x) =>
        graph.addNode(s"{Log|{${expr.min}|${expr.max}}}", shape = "record")
      case Mod(dividend, divisor) =>
        graph.addNode(s"{${patch("%")}|{${expr.min}|${expr.max}}}", shape = "record")
      case Prod(factors) =>
        graph.addNode(s"{${patch("*")}|{${expr.min}|${expr.max}}}", shape = "record")
      case Sum(terms) =>
        graph.addNode(s"{${patch("+")}|{${expr.min}|${expr.max}}}", shape = "record")
      case IntDiv(n, d) =>
        graph.addNode(s"{${patch("/")}|{${expr.min}|${expr.max}}}", shape = "record")
      case IfThenElse(i, t, e) =>
        graph.addNode(patch("if"), shape = "diamond")
      case ? =>
        graph.addNode("?", color = "\"#b58900\"")
      case _ =>
        graph.addNode("???", color = "red")
    }

    val id: Int = node.id

    // explore children
    expr match {
      case ArithExprFunction(_, f) =>
        dot(f.min, graph, id)
        dot(f.max, graph, id)
      case Var(a, b) =>
      //dot(b.min, graph, id)
      case Pow(base, exp) =>
        dot(base, graph, id)
        dot(exp, graph, id)
      case Log(b, x) =>
        dot(b, graph, id)
        dot(x, graph, id)
      case Mod(dividend, divisor) =>
        dot(dividend, graph, id)
        dot(divisor, graph, id)
      case Prod(factors) =>
        factors.map(dot(_, graph, id))
      case Sum(terms) =>
        terms.map(dot(_, graph, id))
      case IntDiv(n, d) =>
        dot(n, graph, id)
        dot(d, graph, id)

      case IfThenElse(i, t, e) =>
        val lhs_g = new DotGraph(true, "LHS")
        val lhs = dot(i.lhs, lhs_g)
        graph.addNode(lhs_g)
        graph.addEdge(id, lhs)

        val rhs_g = new DotGraph(true, "RHS")
        val rhs = dot(i.rhs, rhs_g)
        graph.addNode(rhs_g)
        graph.addEdge(id, rhs)

        val op = graph.addNode(i.op.toString).id
        graph.addEdge(lhs, op)
        graph.addEdge(rhs, op)

        val t_g = new DotGraph(true, "Then")
        val t_n = dot(t, t_g)
        graph.addNode(t_g)
        graph.addEdge(op, t_n)

        val e_g = new DotGraph(true, "Else")
        val e_n = dot(e, e_g)
        graph.addNode(e_g)
        graph.addEdge(op, e_n)
      case _ =>
    }

    if (parent != -1) {
      graph.addEdge(parent, node.id)
    } else if (!graph.isSubgraph) {
      val f = new File("Expr" + graph.gid + ".dot")
      val p = new java.io.PrintWriter(f)
      try { p.write(graph.toString()) } finally { p.close() }
    }
    id
  }
}
