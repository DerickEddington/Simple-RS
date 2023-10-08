use std::cell::{RefCell};

type NodeID = usize;

// These types are part of a Monotone Analysis Framework,
// @see <a href="https://www.cse.psu.edu/~gxt29/teaching/cse597s21/slides/08monotoneFramework.pdf">see for example this set of slides</a>.
//
// The types form a lattice; @see <a href="https://en.wikipedia.org/wiki/Lattice_(order)">a symmetric complete bounded (ranked) lattice.</a>
//
// This wild lattice theory will be needed later to allow us to easily beef up
// the analysis and optimization of the Simple compiler... but we don't need it
// now, just know that it is coming along in a later Chapter.
//
// One of the fun things here is that while the theory is deep and subtle, the
// actual implementation is darn near trivial and is generally really obvious
// what we're doing with it.  Right now, it's just simple integer math to do
// simple constant folding e.g. 1+2 == 3 stuff.
#[derive(Clone, Copy, Debug)]
enum Type {
    Bottom,
    // Integer Type
    Integer{ _con: i64 }
}

#[derive(Clone, Debug)]
enum NodeOp {

    None,

    // The Return node has two inputs.  The first input is a control node and the
    // second is the data node that supplies the return value.
    //
    // In this presentation, Return functions as a Stop node, since multiple <code>return</code>
    // statements are not possible.
    // The Stop node will be introduced in Chapter 6 when we implement <code>if</code> statements.
    //
    // The Return's output is the value from the data node.
    Return,

    // The Start node represents the start of the function.  For now, we do not have any inputs
    // to Start because our function does not yet accept parameters.  When we add parameters the
    // value of Start will be a tuple, and will require Projections to extract the values.
    // We discuss this in detail in Chapter 9: Functions and Calls.
    Start,

    // A Constant node represents a constant value.  At present, the only constants
    // that we allow are integer literals; therefore Constants contain an integer
    // value. As we add other types of constants, we will refactor how we represent
    // Constants.
    //
    // Constants have no semantic inputs. However, we set Start as an input to
    // Constants to enable a forward graph walk.  This edge carries no semantic
    // meaning, and it is present <em>solely</em> to allow visitation.
    //
    // The Constant's value is the value stored in it.
    Constant { _type: Type },

    // Add two integers
    Add,

    // Subtract an integer from another
    Sub,

    // Multiply two integers
    Mul,

    // Integer division
    Div,

    // Unary minus
    Minus,
}

// All Nodes in the Sea of Nodes IR inherit common data from NodeData.
// The NodeData provides common functionality used by all subtypes.
#[derive(Clone, Debug)]
struct Node {
    // Each node has a unique dense Node ID within a compilation context
    // The ID is useful for debugging, for using as an offset in a bitvector,
    // as well as for computing equality of nodes (to be implemented later).
    _nid: NodeID,

    // Type of node - may have additional fields that are type
    // specific
    _op: NodeOp,

    // Inputs to the node. These are use-def references to Nodes.
    //
    // Generally fixed length, ordered, nulls allowed, no unused trailing space.
    // Ordering is required because e.g. "a/b" is different from "b/a".
    // The first input (offset 0) is often a Control node.
    _inputs: RefCell<Vec<NodeID>>,

    // Outputs reference Nodes that are not null and have this Node as an
    // input.  These nodes are users of this node, thus these are def-use
    // references to Nodes.
    //
    // Outputs directly match inputs, making a directed graph that can be
    // walked in either direction.  These outputs are typically used for
    // efficient optimizations but otherwise have no semantics meaning.
    _outputs: RefCell<Vec<NodeID>>,
}

struct Lexer {
    // Input buffer; an array of text bytes read from a file or a string
    _input: Vec<char>,
    // Tracks current position in input buffer
    _position: usize,
}

struct NodePool {
    _nodes: RefCell<Vec<Node>>
}

const _NONE : NodeID = 0 as NodeID;
const _START : NodeID = 1 as NodeID;

struct Parser {
    _lexer: Lexer,
    _pool: NodePool
}

impl Type {
    fn is_constant(&self) -> bool {
        match self {
            Type::Integer{_con} => true,
            _ => false
        }
    }
}

// All nodes are instantiated inside a pool
// This is firstly so that we can pass around NodeIDs and keep
// Rust happy
// But also because we will be using the pool to find nodes
// that are the same, and reuse them in later chapters
impl NodePool {
    fn new() -> Self {
        let pool = NodePool {
            _nodes: RefCell::new(Vec::new())
        };
        pool
    }

    pub fn add(&self, node: NodeOp) -> NodeID {
        let mut pool = self._nodes.borrow_mut();
        let id = pool.len();
        pool.push(Node {
            _nid: id,
            _op: node,
            _inputs: RefCell::new(Vec::new()),
            _outputs: RefCell::new(Vec::new()),
        });
        id
    }

    fn get(&self, nid: NodeID) -> &Node {
        self._nodes.borrow().get(nid).expect("Invalid node id: get failed")
    }
}

impl Node {

    fn new(pool: &NodePool, op: NodeOp, inputs: &Vec<NodeID>) -> NodeID {
        let my_id = pool.add(op);
        let me = pool.get(my_id);
        me.copy_inputs(inputs);
        for n in inputs {
            let user = pool.get(*n);
            user.add_output(my_id);
        }
        my_id
    }

    fn copy_inputs(&self, source: &Vec<NodeID>) {
        let mut inputs = self._inputs.borrow_mut();
        inputs.clear();
        for nid in source {
            inputs.push(*nid)
        }
    }

    fn ctrl(&self) -> NodeID {
        match self._op {
            NodeOp::Return => self._inputs.borrow()[0],
            _ => panic!("ctrl node not available"),
        }
    }
    fn expr(&self) -> NodeID {
        match self._op {
            NodeOp::Return => self._inputs.borrow()[1],
            _ => panic!("expr node not available"),
        }
    }

    // Add supplied NodeID to outputs
    fn add_input(&self, n: NodeID, pool: &NodePool) {
        self._inputs.borrow_mut().push(n);
        let other = pool.get(n);
        other.add_output(self._nid)
    }

    // Add supplied NodeID to outputs
    fn add_output(&self, n: NodeID) {
        self._outputs.borrow_mut().push(n);
    }

    fn move_last_output(&self, idx: usize) -> bool {
        let mut outputs = self._outputs.borrow_mut();
        if outputs.len() > 1 && idx < outputs.len() {
            outputs[idx] = outputs.pop().unwrap();
            true
        }
        else {
            false
        }
    }

    fn get_type(&self) -> Type {
        match self._op {
            NodeOp::Constant {_type} => _type,
            _ => Type::Bottom
        }
    }

    // Kill a Node with no <em>uses</em>, by setting all of its <em>defs</em>
    // to null.  This may recursively kill more Nodes and is basically dead
    // code elimination.  This function is co-recursive with {@link #set_def}.
    fn kill(&self, pool: &NodePool) {
        for i in 0..self._inputs.borrow().len() {
            let kill_node = self.set_def(i, _NONE, pool);
            if kill_node != _NONE {

            }
        }
    }

    fn find_output(&self, n: NodeID) -> Option<usize> {
        self._outputs.borrow().iter().position(|&r| r == n)
    }

    // Change a <em>def</em> into a Node.  Keeps the edges correct, by removing
    // the corresponding <em>use->def</em> edge.  This may make the original
    // <em>def</em> go dead.  This function is co-recursive with {@link #kill}.
    //     
    // @param idx which def to set
    // @param new_def the new definition
    fn set_def(&self, idx: usize, new_def: NodeID, pool: &NodePool) -> NodeID {
        let mut kill_node = _NONE;
        let old_def = self.inp(idx);
        if old_def != _NONE { // If the old def exists, remove a use->def edge
            let old_def_node = pool.get(old_def);
            // Find this node in the other nodes outputs
            let my_idx = old_def_node.find_output(self._nid).unwrap();
            // Move the last node to this node's place
            if !old_def_node.move_last_output(my_idx) { // If we removed the last use, the old def is now dead
                kill_node = old_def;                       // Kill old def
            }
        }
        // Set the new_def over the old (killed) edge
        self._inputs.borrow_mut()[idx] = new_def;
        // If new def is not null, add the corresponding use->def edge
        if new_def != _NONE {
            let new_def_node = pool.get(new_def);
            new_def_node.add_output(self._nid)
        }
        kill_node
    }

    fn inp(&self, idx: usize) -> NodeID {
        self._inputs.borrow()[idx]
    }

    fn add(&self, pool: &NodePool) -> Type {
        let in1 = pool.get(self.inp(1));
        let in2 = pool.get(self.inp(2));
        match in1.get_type() {
            Type::Integer { _con } => {
                let con1 = _con;
                match in2.get_type() {
                    Type::Integer { _con } => {
                        let con2 = _con;
                        Type::Integer { _con: con1 + con2 }
                    },
                    _ => Type::Bottom
                }
            },
            _ => Type::Bottom
        }
    }

    fn sub(&self, pool: &NodePool) -> Type {
        let in1 = pool.get(self.inp(1));
        let in2 = pool.get(self.inp(2));
        match in1.get_type() {
            Type::Integer { _con } => {
                let con1 = _con;
                match in2.get_type() {
                    Type::Integer { _con } => {
                        let con2 = _con;
                        Type::Integer { _con: con1 - con2 }
                    },
                    _ => Type::Bottom
                }
            },
            _ => Type::Bottom
        }
    }

    fn mul(&self, pool: &NodePool) -> Type {
        let in1 = pool.get(self.inp(1));
        let in2 = pool.get(self.inp(2));
        match in1.get_type() {
            Type::Integer { _con } => {
                let con1 = _con;
                match in2.get_type() {
                    Type::Integer { _con } => {
                        let con2 = _con;
                        Type::Integer { _con: con1 * con2 }
                    },
                    _ => Type::Bottom
                }
            },
            _ => Type::Bottom
        }
    }

    fn div(&self, pool: &NodePool) -> Type {
        let in1 = pool.get(self.inp(1));
        let in2 = pool.get(self.inp(2));
        match in1.get_type() {
            Type::Integer { _con } => {
                let con1 = _con;
                match in2.get_type() {
                    Type::Integer { _con } => {
                        let con2 = _con;
                        if con2 == 0 { panic!("divide by zero"); }
                        Type::Integer { _con: con1 / con2 }
                    },
                    _ => Type::Bottom
                }
            },
            _ => Type::Bottom
        }
    }

    fn minus(&self, pool: &NodePool) -> Type {
        let in1 = pool.get(self.inp(1));
        match in1.get_type() {
            Type::Integer { _con } => {
                let con = _con;
                Type::Integer { _con: -con }
            },
            _ => Type::Bottom
        }
    }

    fn compute(&self, pool: &NodePool) -> Type {
        match self._op {
            NodeOp::Add => self.add(pool),
            NodeOp::Sub => self.sub(pool),
            NodeOp::Mul => self.mul(pool),
            NodeOp::Div => self.div(pool),
            NodeOp::Minus => self.minus(pool),
            _ => Type::Bottom
        }
    }

    fn peephole(&self, pool: &NodePool) -> NodeID {
        let computed_type = self.compute(pool);
        match self._op {
            NodeOp::Constant { _type } => self._nid,
            _ => {
                if computed_type.is_constant() {
                    self.kill(pool);
                    Node::new(pool, NodeOp::Constant { _type: computed_type }, &vec![_START])
                }
                else {
                    self._nid
                }
            }
        }
    }
}


impl Parser {
    fn new(source: String) -> Self {
        let parser = Parser {
            _lexer: Lexer {
                _input: source.chars().collect(),
                _position: 0,
            },
            _pool: NodePool::new()
        };
        // Create a None node at with _nid=0
        let none = Node::new(&parser._pool, NodeOp::None, &vec![]);
        let start = Node::new(&parser._pool, NodeOp::Start, &vec![]);
        if none != _NONE || start != _START {
            panic!("Unexpected error: initial nodes do not have expected values");
        }
        parser
    }

    fn parse(&mut self) -> NodeID {
        self.require(String::from("return"));        
        self.parse_return()
    }

    // Parses return statement.
    // return expr ;
    fn parse_return(&mut self) -> NodeID {
        let return_expr = self.parse_expression();
        self.require(String::from(";"));
        self.new_return(_START, return_expr)
    }

    // Parse an expression of the form:
    // expr : primaryExpr
    fn parse_expression(&mut self) -> NodeID {
        self.parse_addition()
    }

    fn parse_addition(&mut self) -> NodeID {
        let lhs_id = self.parse_multiplication();
        if self._lexer.match_string(String::from("+")) {
            let rhs_id = self.parse_addition();
            let add_id = Node::new(&self._pool, NodeOp::Add, &vec![_NONE, lhs_id, rhs_id]);
            let add_node = self._pool.get(add_id);
            add_node.peephole(&self._pool)
        }
        else if self._lexer.match_string(String::from("-")) {
            let rhs_id = self.parse_addition();
            let sub_id = Node::new(&self._pool, NodeOp::Sub, &vec![_NONE, lhs_id, rhs_id]);
            let sub_node = self._pool.get(sub_id);
            sub_node.peephole(&self._pool)
        }
        else {
            lhs_id
        }
    }

    fn parse_multiplication(&mut self) -> NodeID {
        let lhs_id = self.parse_unary();
        if self._lexer.match_string(String::from("*")) {
            let rhs_id = self.parse_multiplication();
            let mul_id = Node::new(&self._pool, NodeOp::Mul, &vec![_NONE, lhs_id, rhs_id]);
            let mul_node = self._pool.get(mul_id);
            mul_node.peephole(&self._pool)
        }
        else if self._lexer.match_string(String::from("/")) {
            let rhs_id = self.parse_multiplication();
            let div_id = Node::new(&self._pool, NodeOp::Div, &vec![_NONE, lhs_id, rhs_id]);
            let div_node = self._pool.get(div_id);
            div_node.peephole(&self._pool)
        }
        else {
            lhs_id
        }
    }

    fn parse_unary(&mut self) -> NodeID {
        if self._lexer.match_string(String::from("-")) {
            let unary = self.parse_unary();
            let nid = Node::new( &self._pool, NodeOp::Minus, &vec![_NONE, unary]);
            let node = self._pool.get(nid);
            node.peephole(&self._pool)
        }
        else {
            self.parse_primary()
        }
    }

    // Parse a primary expression:
    // primaryExpr : integerLiteral
    fn parse_primary(&mut self) -> NodeID {
        self._lexer.skip_whitespace();
        if self._lexer.is_number() {
            return self.parse_integer_literal();
        }
        if self._lexer.match_string(String::from("(")) {
            let expr = self.parse_expression();
            return self.require_and_node(expr, String::from(")"));
        }
        panic!("Syntax error: expected integer literal or nested expression");
    }

    // Parse integer literal
    // integerLiteral: [1-9][0-9]* | [0]
    fn parse_integer_literal(&mut self) -> NodeID {
        let value = self._lexer.parse_number();
        let nid = self.new_constant(value);
        let node = self._pool.get(nid);
        node.peephole(&self._pool)
    }

    fn require(&mut self, syntax: String) {
        if self._lexer.match_string(syntax) {
            return;
        }
        panic!();
    }

    fn require_and_node(&mut self, n: NodeID, syntax: String) -> NodeID {
        if self._lexer.match_string(syntax) {
            return n;
        }
        panic!("Syntax error");
    }

    // Create ReturnNode
    fn new_return(&mut self, ctrl: NodeID, data: NodeID) -> NodeID {
        Node::new(&self._pool, NodeOp::Return, &vec![ctrl, data])
    }

    // Create ConstantNode
    fn new_constant(&mut self, value: Type) -> NodeID {
        Node::new(&self._pool, NodeOp::Constant { _type: value }, &vec![_START])
    }

    // create StartNode
    fn new_start(&mut self) -> NodeID {
        Node::new(&self._pool, NodeOp::Start, &vec![])
    }

}

const EOF_CHAR : char = 0 as char;

impl Lexer {
    // True if at EOF
    fn is_eof(&self) -> bool {
        self._position >= self._input.len()
    }

    fn peek(&self) -> char {
        if self.is_eof() {
            EOF_CHAR
        } else {
            self._input[self._position]
        }
    }

    fn next_char(&mut self) -> char {
        let ch = self.peek();
        self._position += 1;
        ch
    }

    // True if a white space
    fn is_white_space(&self) -> bool {
        match self.peek() {
            ' ' | '\t' | '\n' | '\r' => true,
            _ => false
        }
    }

    fn skip_whitespace(&mut self) {
        while self.is_white_space() {
            self._position += 1;
        }
    }

    // Return true, if we find "syntax" after skipping white space; also
    // then advance the cursor past syntax.
    // Return false otherwise, and do not advance the cursor.
    fn match_string(&mut self, syntax: String) -> bool {
        self.skip_whitespace();
        let chars: Vec<_> = syntax.chars().collect();
        let len = syntax.len();
        if self._position + len > self._input.len() {
            return false;
        }
        for i in 0..len {
            if self._input[self._position + i] != chars[i] {
                return false;
            }
        }
        self._position += len;
        true
    }

    fn is_digit(&self, ch: char) -> bool {
        ch.is_numeric()
    }

    fn is_number(&self) -> bool {
        self.is_digit(self.peek())
    }

    fn parse_number(&mut self) -> Type {
        let mut ch = self.next_char();
        let mut chars: Vec<char> = vec![];
        while self.is_digit(ch) {
            chars.push(ch);
            ch = self.next_char();
        }
        self._position -= 1;
        let snum: String = chars.into_iter().collect();
        let num = snum.parse::<i64>()
            .expect("Unexpected failure parsing number");
        Type::Integer { _con: num }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexer() {
        let mut parser = Parser::new(String::from("return 1"));
        let mut c = parser._lexer.next_char();
        assert_eq!(c, 'r');
        c = parser._lexer.next_char();
        assert_eq!(c, 'e');
    }

    #[test]
    fn test_lexer_match_string() {
        let mut parser = Parser::new(String::from("  return 1"));
        assert!(parser._lexer.match_string(String::from("return")));
    }

    // #[test]
    // fn test_lexer_parse_number() {
    //     let mut parser = Parser::new(String::from("42"));
    //     assert_eq!(42, parser._lexer.parse_number());
    // }

    // #[test]
    // fn test_parse() {
    //     let mut parser = Parser::new(String::from("return 42;"));
    //     let n = parser.parse();
    //     let return_node = parser._nodes.get(n);
    //     match return_node._op {
    //         NodeOp::Return => {
    //             // control input must be START
    //             let ctrl_n = return_node.ctrl();
    //             assert_eq!(ctrl_n, _START);
    //             // data input must be the constant
    //             let data_n = return_node.expr();
    //             let constant_node = parser._nodes.get(data_n);
    //             match constant_node._op {
    //                 NodeOp::Constant { _value } => {
    //                     assert_eq!(constant_node._inputs.len(), 1);
    //                     assert_eq!(42, _value);
    //                     assert_eq!(parser._START, constant_node._inputs[0]) // START node
    //                 }
    //                 _ => assert!(false),
    //             }
    //             let start_node = parser._nodes.get(ctrl_n);
    //             match start_node._op {
    //                 NodeOp::Start => {
    //                     assert_eq!(0, start_node._inputs.len());
    //                 }
    //                 _ => assert!(false),
    //             }
    //         }
    //         _ => assert!(false),
    //     }
    // }
}
