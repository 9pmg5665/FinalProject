package widegraphlayout;

import java.awt.Rectangle;
import java.awt.geom.Point2D;
import java.awt.Point;
import java.util.*;

import javax.swing.Icon;

import generic.stl.Pair;
import ghidra.app.plugin.core.functiongraph.graph.FGEdge;
import ghidra.app.plugin.core.functiongraph.graph.FunctionGraph;
import ghidra.app.plugin.core.functiongraph.graph.layout.AbstractFGLayout;
import ghidra.app.plugin.core.functiongraph.graph.layout.FGLayout;
import ghidra.app.plugin.core.functiongraph.graph.layout.FGLayoutProvider;
import ghidra.app.plugin.core.functiongraph.graph.vertex.FGVertex;
import ghidra.graph.VisualGraph;
import ghidra.graph.viewer.layout.*;
import ghidra.graph.viewer.vertex.VisualGraphVertexShapeTransformer;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;
import resources.ResourceManager;

public class ControlFlowChart extends FGLayoutProvider {

	private static final String NAME = "Control Flow Test";
	private static final double PADDING_JUNCTIONS = 30.0;
	private static final double OFFSET_JUNCTIONS = 10.0;



	private class Node {

		private FGVertex v;

		private int row;
		private int col;

		Node(FGVertex v, int row, int col) {
			this.v = v;
			this.row = row;
			this.col = col;
		}

		Node(FGVertex v) {
			this.v = v;
			this.row = 0;
			this.col = 0;
		}

		public int hashCode() {
			return (int) this.v.getVertexAddress().getOffset();
		}

		public boolean equals(Object o) {
			if (o.getClass() != this.getClass())
				return false;
			Node on = (Node) o;
			return this.v.getVertexAddress().getOffset() == on.v.getVertexAddress().getOffset();
		}

		@Override
		public String toString() {
			return "Node [ " + v + ", " + row + ", " + col + " ]";
		}
	}
	
	private class FlowGraph extends AbstractFGLayout {

		private HashMap<Integer, List<Node>> rows;
		private HashMap<FGVertex, Node> verts;
		private HashMap<FGEdge, List<Point>> junctions;
		private HashMap<Point, List<FGEdge>> reverseJunctions;
		private HashMap<Pair<Integer, FGEdge>, Double> xBox;
		private HashMap<Pair<Integer, FGEdge>, Double> yBox;

		private int max_col = -1;

		protected FlowGraph(FunctionGraph graph) {
			super(graph, NAME);

			rows = new HashMap<>();
			verts = new HashMap<>();
			junctions = new HashMap<>();
			reverseJunctions = new HashMap<>();
			xBox = new HashMap<>();
			yBox = new HashMap<>();

		}

		@Override
		protected AbstractVisualGraphLayout<FGVertex, FGEdge> createClonedFGLayout(FunctionGraph Graph) {
			return new FlowGraph(Graph);
		}

		@Override
		protected Point2D getVertexLocation(FGVertex v, Column col, Row<FGVertex> row, Rectangle bounds) {
			return getCenteredVertexLocation(v, col, row, bounds);
		}

		private void resetLayout() {
			rows.clear();
			verts.clear();
			junctions.clear();
			reverseJunctions.clear();
			xBox.clear();
			yBox.clear();

			max_col = -1;
		}

		@Override
		protected GridLocationMap<FGVertex, FGEdge> performInitialGridLayout(VisualGraph<FGVertex, FGEdge> g)
				throws CancelledException {

			GridLocationMap<FGVertex, FGEdge> gridLocations = new GridLocationMap<>();

			Collection<FGVertex> vertices = g.getVertices();
			Collection<FGEdge> edges = g.getEdges();
			List<FGVertex> sorted_vertices = new ArrayList<>(vertices);
			Collections.sort(sorted_vertices, (v1, v2) -> v1.getVertexAddress().compareTo(v2.getVertexAddress()));

			if (sorted_vertices.size() == 0)
				return gridLocations;

			Iterator<FGVertex> it = sorted_vertices.iterator();
			FGVertex root = it.next();
			resetLayout();

			assignRows(g, root);
			assignCols(g, root);
			assignJunctions(edges);
			assignJunctionPadding();
			populateGrid(gridLocations);

			return gridLocations;
		}

		private void assignRows(VisualGraph<FGVertex, FGEdge> g, FGVertex root) {
			class Closure {
				void run(FGVertex vertex, Set<FGVertex> path, int row) {
					if (path.contains(vertex))
						return;

					Collection<FGVertex> successors = g.getSuccessors(vertex);

					if (!rows.containsKey(row))
						rows.put(row, new ArrayList<Node>());

					Node n;
					if (verts.containsKey(vertex)) {
						n = verts.get(vertex);
						if (n.row < row) {
							List<Node> list_row = rows.get(n.row);
							boolean res = list_row.remove(n);
							assert (res);
							rows.get(row).add(n);
							n.row = row;
						} else
							return;
					} else {
						n = new Node(vertex, row, 0);
						verts.put(vertex, n);
						rows.get(row).add(n);
					}

					for (FGVertex s : successors) {
						Set<FGVertex> newPath = new HashSet<>(path);
						newPath.add(vertex);
						run(s, newPath, row + 1);
					}
				}
			}
			new Closure().run(root, new HashSet<FGVertex>(), 0);
		}

		private void assignCols(VisualGraph<FGVertex, FGEdge> g, FGVertex root) {
			class Closure {
				int assignScores(Set<FGVertex> visited, Map<FGVertex, Integer> vertexScores, Set<FGVertex> path,
						FGVertex vertex, int score) {
					if (visited.contains(vertex)) {
						if (path.contains(vertex))
							return -1000;
						return 0;
					}

					visited.add(vertex);

					int subnodes = 0;
					Collection<FGVertex> successors = g.getSuccessors(vertex);
					for (FGVertex s : successors) {
						HashSet<FGVertex> newPath = new HashSet<>(path);
						newPath.add(vertex);
						subnodes += assignScores(visited, vertexScores, newPath, s, score + subnodes + 1);
					}
					vertexScores.put(vertex, score + subnodes + 1);
					return subnodes;
				}
			}
			HashMap<FGVertex, Integer> vertexScores = new HashMap<>();
			new Closure().assignScores(new HashSet<FGVertex>(), vertexScores, new HashSet<FGVertex>(), root, 0);

			int max_row_len = Collections.max(rows.values(), (l1, l2) -> l1.size() - l2.size()).size();
			for (Integer row : rows.keySet()) {
				List<Node> nodes_row = rows.get(row);
				Collections.sort(nodes_row, (n1, n2) -> vertexScores.get(n1.v) - vertexScores.get(n2.v));

				int row_len = nodes_row.size();
				int offset = (max_row_len - row_len) / 2;

				int i = 0;
				for (Node n : nodes_row) {
					n.col = offset + i;
					if (n.col > max_col)
						max_col = n.col;
					i += 1;
				}
			}

		}

		private int getEdgeRow(int row) {
			return 2 * row + 1;
		}

		private int getEdgeCol(int col) {
			return 2 * col + 1;
		}

		private int getBottomEdgeRow(int row) {
			return 2 * row + 2;
		}

		private int getTopEdgeRow(int row) {
			return 2 * row;
		}

		private int getRightEdgeCol(int col) {
			return 2 * col + 2;
		}

		private int getLeftEdgeCol(int col) {
			return 2 * col;
		}

		private int sortEdges(FGEdge e1, FGEdge e2) {
			int srcRow1 = verts.get(e1.getStart()).row;
			int srcCol1 = verts.get(e1.getStart()).col;
			int dst_row_1 = verts.get(e1.getEnd()).row;
			int dst_col_1 = verts.get(e1.getEnd()).col;

			int srcRow2 = verts.get(e2.getStart()).row;
			int srcCol2 = verts.get(e2.getStart()).col;
			int dst_row_2 = verts.get(e2.getEnd()).row;
			int dst_col_2 = verts.get(e2.getEnd()).col;

			if (dst_row_1 < dst_row_2)
				return -1;
			else if (dst_row_2 < dst_row_1)
				return 1;

			if (srcRow1 > srcRow2)
				return -1;
			else if (srcRow2 > srcRow1)
				return 1;

			if (dst_col_1 < dst_col_2)
				return -1;
			else if (dst_col_2 < dst_col_1)
				return 1;

			if (srcCol1 < srcCol2)
				return -1;
			else if (srcCol2 < srcCol1)
				return 1;

			return 0;
		}

		private boolean detectEdgeClash(Collection<FGEdge> edges, FGEdge edge) {
			/*
			 *Detection of collisions
			 */

			FGVertex vSrc = edge.getStart();
			FGVertex vDst = edge.getEnd();
			Node vSrcn = verts.get(vSrc);
			Node vDstn = verts.get(vDst);

			for (FGEdge e : edges) {
				FGVertex src = e.getStart();
				FGVertex dst = e.getEnd();
				Node srcn = verts.get(src);
				Node dstn = verts.get(dst);

				if (srcn.row < vSrcn.row || (srcn.row == vSrcn.row && srcn.col > vSrcn.col)) {
					if (dstn.row == vSrcn.row + 1 && dstn.col <= vSrcn.col) {
						return true;
					}
				}
			}
			return false;
		}

		private int maxColInRange(int row_min, int row_max) {
			// slow AF. Refactor it
			int col_max = 0;
			for (FGVertex v : verts.keySet()) {
				Node n = verts.get(v);
				if (n.row >= row_min && n.row <= row_max)
					if (n.col > col_max)
						col_max = n.col;
			}
			return col_max;
		}

		private void addJunction(Point p, FGEdge e) {
			if (!junctions.containsKey(e))
				junctions.put(e, new ArrayList<Point>());
			junctions.get(e).add(new Point(p));
			if (!reverseJunctions.containsKey(p))
				reverseJunctions.put(p, new ArrayList<FGEdge>());
			reverseJunctions.get(p).add(e);
		}

		private void assignJunctions(Collection<FGEdge> edges) {
			ArrayList<FGEdge> sorted_edges = new ArrayList<FGEdge>(edges);
			Collections.sort(sorted_edges, (e1, e2) -> {
				return sortEdges(e1, e2);
			});

			for (FGEdge e : edges) {
				FGVertex startVertex = e.getStart();
				FGVertex endVertex = e.getEnd();
				Node startNode = verts.get(startVertex);
				Node endNode = verts.get(endVertex);

				Direction x, y;
				if (startNode.col == endNode.col)
					x = Direction.STILL;
				else if (startNode.col < endNode.col)
					x = Direction.RIGHT;
				else
					x = Direction.LEFT;

				if (startNode.row == endNode.row)
					y = Direction.STILL;
				else if (startNode.row > endNode.row)
					y = Direction.UP;
				else
					y = Direction.DOWN;

				if (y == Direction.DOWN) {
					// descend right, if clash, try descend left
					int start_row = startNode.row;
					int end_row = endNode.row;

					// descend at junction level
					Point p0 = new Point(getEdgeCol(startNode.col), getBottomEdgeRow(startNode.row));
					addJunction(p0, e);

					if (end_row - start_row > 1) {
						// if multiple levels, turn around the right column. If clash, turn around the
						// left column
						if (detectEdgeClash(edges, e)) {
							Point p1 = new Point(getLeftEdgeCol(endNode.col), getBottomEdgeRow(startNode.row));
							addJunction(p1, e);

							Point p2 = new Point(getLeftEdgeCol(endNode.col), getTopEdgeRow(endNode.row));
							addJunction(p2, e);
						} else {
							int col = getRightEdgeCol(maxColInRange(startNode.row, endNode.row));
							Point p1 = new Point(col, getBottomEdgeRow(startNode.row));
							addJunction(p1, e);

							Point p2 = new Point(col, getTopEdgeRow(endNode.row));
							addJunction(p2, e);
						}
					}

					// descend
					Point p3 = new Point(getEdgeCol(endNode.col), getTopEdgeRow(endNode.row));
					addJunction(p3, e);

				} else {
					// ascend always left
					x = Direction.LEFT;

					// descend at junction level
					Point p0 = new Point(getEdgeCol(startNode.col), getBottomEdgeRow(startNode.row));
					addJunction(p0, e);

					// go to destination left column
					Point p1 = new Point(getLeftEdgeCol(endNode.col), getBottomEdgeRow(startNode.row));
					addJunction(p1, e);

					// go up to vertedEnd row
					Point p2 = new Point(getLeftEdgeCol(endNode.col), getTopEdgeRow(endNode.row));
					addJunction(p2, e);

					// descend
					Point p3 = new Point(getEdgeCol(endNode.col), getTopEdgeRow(endNode.row));
					addJunction(p3, e);

					e.setEmphasis(0.2);
				}
			}
		}

		private void assignJunctionPadding() {
			// slow AF. Rewrite this
			Map<Integer, Set<FGEdge>> edge_per_row = new HashMap<>();
			Map<Integer, Set<FGEdge>> edge_per_col = new HashMap<>();

			for (Point p : reverseJunctions.keySet()) {
				if (!edge_per_row.containsKey(p.x))
					edge_per_row.put(p.x, new HashSet<>());
				edge_per_row.get(p.x).addAll(reverseJunctions.get(p));

				if (!edge_per_col.containsKey(p.y))
					edge_per_col.put(p.y, new HashSet<>());
				edge_per_col.get(p.y).addAll(reverseJunctions.get(p));
			}

			for (int x : edge_per_row.keySet()) {

				Map<Integer, Integer> off_map = new HashMap<>();

				Pair<Integer, FGEdge> off;
				List<FGEdge> sorted_edges_per_row = new ArrayList<>(edge_per_row.get(x));
				Collections.sort(sorted_edges_per_row, (e1, e2) -> {
					return sortEdges(e1, e2);
				});
				for (FGEdge e : sorted_edges_per_row) {
					List<Point> junctions_edge = junctions.get(e);

					int min_col = Integer.MAX_VALUE;
					int max_col = 0;
					for (Point p : junctions_edge) {
						if (p.x != x)
							continue;
						if (p.y <= min_col)
							min_col = p.y;
						if (p.y >= max_col)
							max_col = p.y;
					}

					int v = 0;
					for (int i = min_col; i <= max_col; ++i) {
						if (!off_map.containsKey(i))
							off_map.put(i, 0);
						int off_v = off_map.get(i);
						if (off_v >= v)
							v = off_v + 1;
					}
					for (int i = min_col; i <= max_col; ++i)
						off_map.put(i, v);
					off = new Pair<>(x, e);
					xBox.put(off, -PADDING_JUNCTIONS + v * OFFSET_JUNCTIONS);
				}
			}

			for (int y : edge_per_col.keySet()) {
				Map<Integer, Integer> off_map = new HashMap<>();

				Pair<Integer, FGEdge> off;
				List<FGEdge> sorted_edges_per_col = new ArrayList<>(edge_per_col.get(y));
				Collections.sort(sorted_edges_per_col, (e1, e2) -> {
					return sortEdges(e1, e2);
				});
				for (FGEdge e : sorted_edges_per_col) {
					List<Point> junctions_edge = junctions.get(e);

					int min_row = Integer.MAX_VALUE;
					int max_row = 0;
					for (Point p : junctions_edge) {
						if (p.y != y)
							continue;
						if (p.x <= min_row)
							min_row = p.x;
						if (p.x >= max_row)
							max_row = p.x;
					}

					int v = 0;
					for (int i = min_row; i <= max_row; ++i) {
						if (!off_map.containsKey(i))
							off_map.put(i, 0);
						int off_v = off_map.get(i);
						if (off_v >= v)
							v = off_v + 1;
					}
					for (int i = min_row; i <= max_row; ++i)
						off_map.put(i, v);
					off = new Pair<>(y, e);
					yBox.put(off, -PADDING_JUNCTIONS + v * OFFSET_JUNCTIONS);
				}
			}

		}

		private void populateGrid(GridLocationMap<FGVertex, FGEdge> gridLocations) {
			for (Node n : verts.values())
				gridLocations.set(n.v, n.row * 2 + 1, n.col * 2 + 1);

			for (FGEdge e : junctions.keySet()) {
				gridLocations.setArticulations(e, junctions.get(e));
			}
		}

		@Override
		protected Map<FGEdge, List<Point2D>> positionEdgeArticulationsInLayoutSpace(
				VisualGraphVertexShapeTransformer<FGVertex> transformer, Map<FGVertex, Point2D> vertexLayoutLocations,
				Collection<FGEdge> edges, LayoutLocationMap<FGVertex, FGEdge> layoutLocations)
				throws CancelledException {

			ArrayList<FGEdge> sorted_edges = new ArrayList<FGEdge>(edges);
			Collections.sort(sorted_edges, (e1, e2) -> {
				return sortEdges(e1, e2);
			});

			Map<FGEdge, List<Point2D>> newEdgeArticulations = new HashMap<>();

			for (FGEdge edge : sorted_edges) {
				monitor.checkCanceled();
				List<Point2D> newArticulations = new ArrayList<>();
				List<Point> edgeJunctions = junctions.get(edge);

				int i = 0;
				for (Point gridPoint : layoutLocations.articulations(edge)) {

					Row<FGVertex> row = layoutLocations.row(gridPoint.y);
					Column column = layoutLocations.col(gridPoint.x);
					
					Point junction = edgeJunctions.get(i);
					double rowPadding = xBox.get(new Pair<>(junction.x, edge));
					double colPadding = yBox.get(new Pair<>(junction.y, edge));

					Point2D location = getCenteredEdgeLocation(column, row);
					Point2D newLocation = new Point2D.Double(location.getX() + rowPadding, location.getY() + colPadding);
					newArticulations.add(newLocation);
					i++;
				}

				
				Point2D first_junction = newArticulations.get(0);
				Point2D last_junction = newArticulations.get(newArticulations.size() - 1);
				newArticulations.add(0,
						new Point2D.Double(first_junction.getX(), vertexLayoutLocations.get(edge.getStart()).getY()));
				newArticulations
						.add(new Point2D.Double(last_junction.getX(), vertexLayoutLocations.get(edge.getEnd()).getY()));

				newEdgeArticulations.put(edge, newArticulations);
			}
			return newEdgeArticulations;
		}

		@Override
		protected boolean isCondensedLayout() {
			return false;
		}

		private Direction oppositeDirection(Direction d) {
			switch (d) {
			case STILL:
				return Direction.STILL;
			case UP:
				return Direction.DOWN;
			case DOWN:
				return Direction.UP;
			case LEFT:
				return Direction.RIGHT;
			case RIGHT:
				return Direction.LEFT;
			}
			throw new IllegalArgumentException();
		}

	}

	private enum Direction {
		LEFT, RIGHT, UP, DOWN, STILL
	}

	@Override
	public String getLayoutName() {
		return NAME;
	}

	@Override
	public Icon getActionIcon() {
		return ResourceManager.loadImage("images/chart.png");
	}

	@Override
	public int getPriorityLevel() {
		return 400; 
	}

	@Override
	public FGLayout getFGLayout(FunctionGraph graph, TaskMonitor monitor) throws CancelledException {
		return new FlowGraph(graph);
	}
	
}