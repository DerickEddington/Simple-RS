type NodeID = usize;

#[derive(Clone, Debug)]
enum NodeOp {
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
    Constant { _value: i64 },
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
    _inputs: Vec<NodeID>,

    // Outputs reference Nodes that are not null and have this Node as an
    // input.  These nodes are users of this node, thus these are def-use
    // references to Nodes.
    //
    // Outputs directly match inputs, making a directed graph that can be
    // walked in either direction.  These outputs are typically used for
    // efficient optimizations but otherwise have no semantics meaning.
    _outputs: Vec<NodeID>,
}

struct Lexer {
    // Input buffer; an array of text bytes read from a file or a string
    _input: Vec<char>,
    // Tracks current position in input buffer
    _position: usize,
}

struct NodePool {
    _nodes: Vec<Node>
}

struct Parser {
    _lexer: Lexer,
    // The Start node
    _START: NodeID,
    _nodes: NodePool
}

// All nodes are instantiated inside a pool
// This is firstly so that we can pass around NodeIDs and keep
// Rust happy
// But also because we will be using the pool to find nodes
// that are the same, and reuse them in later chapters
impl NodePool {
    fn new() -> Self {
        let pool = NodePool {
            _nodes: Vec::new()
        };
        pool
    }

    pub fn add(&mut self, node: NodeOp) -> NodeID {
        let id = self._nodes.len();
        self._nodes.push(Node {
            _nid: id,
            _op: node,
            _inputs: Vec::new(),
            _outputs: Vec::new(),
        });
        id
    }

    fn get(&self, nid: NodeID) -> &Node {
        self._nodes.get(nid).expect("Invalid node id: get failed")
    }

    fn get_mut(&mut self, nid: NodeID) -> &mut Node {
        self._nodes
            .get_mut(nid)
            .expect("Invalid node id: get failed")
    }
}

impl Node {

    fn new(pool: &mut NodePool, op: NodeOp, inputs: &Vec<NodeID>) -> NodeID {
        let my_id = pool.add(op);
        let me = pool.get_mut(my_id);
        me._inputs = inputs.clone();
        for n in inputs {
            let user = pool.get_mut(*n);
            user.add_output(my_id);
        }
        my_id
    }

    fn ctrl(&self) -> NodeID {
        match self._op {
            NodeOp::Return => self._inputs[0],
            _ => panic!("ctrl node not available"),
        }
    }
    fn expr(&self) -> NodeID {
        match self._op {
            NodeOp::Return => self._inputs[1],
            _ => panic!("expr node not available"),
        }
    }

    // Get iterator on inputs
    fn inputs(&self) -> std::slice::Iter<'_, NodeID> {
        self._inputs.iter()
    }

    // Add supplied NodeID to outputs
    fn add_input(&mut self, n: NodeID, pool: &mut NodePool) {
        self._inputs.push(n);
        let mut other = pool.get_mut(n);
        other.add_output(self._nid)
    }

    // Add supplied NodeID to outputs
    fn add_output(&mut self, n: NodeID) {
        self._outputs.push(n);
    }
}


impl Parser {
    fn new(source: String) -> Self {
        let mut parser = Parser {
            _lexer: Lexer {
                _input: source.chars().collect(),
                _position: 0,
            },
            _nodes: NodePool::new(),
            _START: 0,
        };
        parser._START = Node::new(&mut parser._nodes, NodeOp::Start, &vec![]);
        parser
    }

    fn parse(&mut self) -> NodeID {
        self.parse_return()
    }

    // Parses return statement.
    // return expr ;
    fn parse_return(&mut self) -> NodeID {
        self.require(String::from("return"));
        let return_expr = self.parse_expression();
        self.require(String::from(";"));
        self.new_return(self._START, return_expr)
    }

    // Parse an expression of the form:
    // expr : primaryExpr
    fn parse_expression(&mut self) -> NodeID {
        self.parse_primary()
    }

    // Parse a primary expression:
    // primaryExpr : integerLiteral
    fn parse_primary(&mut self) -> NodeID {
        self._lexer.skip_whitespace();
        if self._lexer.is_number() {
            return self.parse_integer_literal();
        }
        panic!();
    }

    // Parse integer literal
    // integerLiteral: [1-9][0-9]* | [0]
    fn parse_integer_literal(&mut self) -> NodeID {
        let value = self._lexer.parse_number();
        self.new_constant(value)
    }

    fn require(&mut self, syntax: String) {
        if self._lexer.match_string(syntax) {
            return;
        }
        panic!();
    }

    // Create ReturnNode
    fn new_return(&mut self, ctrl: NodeID, data: NodeID) -> NodeID {
        Node::new(&mut self._nodes, NodeOp::Return, &vec![ctrl, data])
    }

    // Create ConstantNode
    fn new_constant(&mut self, value: i64) -> NodeID {
        Node::new(&mut self._nodes, NodeOp::Constant { _value: value }, &vec![self._START])
    }

    // create StartNode
    fn new_start(&mut self) -> NodeID {
        Node::new(&mut self._nodes, NodeOp::Start, &vec![])
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

    fn parse_number(&mut self) -> i64 {
        let mut ch = self.next_char();
        let mut chars: Vec<char> = vec![];
        while self.is_digit(ch) {
            chars.push(ch);
            ch = self.next_char();
        }
        self._position -= 1;
        let snum: String = chars.into_iter().collect();
        snum.parse::<i64>()
            .expect("Unexpected failure parsing number")
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

    #[test]
    fn test_lexer_parse_number() {
        let mut parser = Parser::new(String::from("42"));
        assert_eq!(42, parser._lexer.parse_number());
    }

    #[test]
    fn test_parse() {
        let mut parser = Parser::new(String::from("return 42;"));
        let n = parser.parse();
        let return_node = parser._nodes.get(n);
        match return_node._op {
            NodeOp::Return => {
                // control input must be START
                let ctrl_n = return_node.ctrl();
                assert_eq!(ctrl_n, parser._START);
                // data input must be the constant
                let data_n = return_node.expr();
                let constant_node = parser._nodes.get(data_n);
                match constant_node._op {
                    NodeOp::Constant { _value } => {
                        assert_eq!(constant_node._inputs.len(), 1);
                        assert_eq!(42, _value);
                        assert_eq!(parser._START, constant_node._inputs[0]) // START node
                    }
                    _ => assert!(false),
                }
                let start_node = parser._nodes.get(ctrl_n);
                match start_node._op {
                    NodeOp::Start => {
                        assert_eq!(0, start_node._inputs.len());
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }
}
