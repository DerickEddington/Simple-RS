type NodeID = usize;

// All Nodes in the Sea of Nodes IR inherit common data from NodeData.
// The NodeData provides common functionality used by all subtypes.
struct NodeData {
    // Each node has a unique dense Node ID within a compilation context
    // The ID is useful for debugging, for using as an offset in a bitvector,
    // as well as for computing equality of nodes (to be implemented later).
    _nid: NodeID,

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

//
enum Node {
    // The Return node has two inputs.  The first input is a control node and the
    // second is the data node that supplies the return value.
    //
    // In this presentation, Return functions as a Stop node, since multiple <code>return</code>
    // statements are not possible.
    // The Stop node will be introduced in Chapter 6 when we implement <code>if</code> statements.
    //
    // The Return's output is the value from the data node.
    ReturnNode { _data: NodeData },

    // The Start node represents the start of the function.  For now, we do not have any inputs
    // to Start because our function does not yet accept parameters.  When we add parameters the
    // value of Start will be a tuple, and will require Projections to extract the values.
    // We discuss this in detail in Chapter 9: Functions and Calls.
    StartNode { _data: NodeData },

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
    ConstantNode { _data: NodeData, _value: i64 },
}

struct Lexer {
    // Input buffer; an array of text bytes read from a file or a string
    _input: Vec<char>,
    // Tracks current position in input buffer
    _position: usize,
}

struct Parser {
    _lexer: Lexer,
    _START: NodeID,
    _nodes: Vec<Box<Node>>,
}

impl Node {
    fn ctrl(&self) -> NodeID {
        match self {
            Node::ReturnNode { _data } => _data._inputs[0],
            _ => panic!(),
        }
    }
    fn expr(&self) -> NodeID {
        match self {
            Node::ReturnNode { _data } => _data._inputs[1],
            _ => panic!(),
        }
    }

    // Get iterator on inputs
    fn inputs(&self) -> std::slice::Iter<'_, NodeID> {
        match self {
            Node::StartNode { _data } | Node::ReturnNode { _data } => _data._inputs.iter(),
            Node::ConstantNode { _data, _value } => _data._inputs.iter(),
        }
    }

    // Add supplied NodeID to outputs
    fn add_output(&mut self, n: NodeID) {
        match self {
            Node::StartNode { _data } | Node::ReturnNode { _data } => {
                _data._outputs.push(n);
            }
            Node::ConstantNode { _data, _value } => {
                _data._outputs.push(n);
            }
        }
    }
}

impl Lexer {
    // True if at EOF
    fn is_eof(&self) -> bool {
        self._position >= self._input.len()
    }

    fn peek(&self) -> char {
        if self.is_eof() {
            char::MAX
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
        self.peek() <= ' '
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

impl Parser {
    fn new(source: String) -> Self {
        let mut parser = Parser {
            _lexer: Lexer {
                _input: source.chars().collect(),
                _position: 0,
            },
            _nodes: vec![],
            _START: 0,
        };
        parser._START = parser.new_start();
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

    fn set_outputs(&mut self, node: &mut Node) {
        for n in node.inputs() {
            if 0 != *n {
                let node = self.get_mut(*n);
                node.add_output(*n);
            }
        }
    }

    // Create ReturnNode
    fn new_return(&mut self, ctrl: NodeID, data: NodeID) -> NodeID {
        let nid = self._nodes.len();
        let mut node = Box::new(Node::ReturnNode {
            _data: NodeData {
                _nid: nid,
                _inputs: vec![ctrl, data],
                _outputs: vec![],
            },
        });
        self.set_outputs(node.as_mut());
        self._nodes.push(node);
        nid
    }

    // Create ConstantNode
    fn new_constant(&mut self, value: i64) -> NodeID {
        let nid = self._nodes.len();
        let mut node = Box::new(Node::ConstantNode {
            _data: NodeData {
                _nid: nid,
                _inputs: vec![self._START],
                _outputs: vec![],
            },
            _value: value,
        });
        self.set_outputs(node.as_mut());
        self._nodes.push(node);
        nid
    }

    // create StartNode
    fn new_start(&mut self) -> NodeID {
        let nid = self._nodes.len();
        let mut node = Box::new(Node::StartNode {
            _data: NodeData {
                _nid: nid,
                _inputs: vec![],
                _outputs: vec![],
            },
        });
        self.set_outputs(node.as_mut());
        self._nodes.push(node);
        nid
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

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn test_return_node() {
    //     let mut parser = Parser::new(String::from("return 1"));
    //     let ret_node_id = parser.new_return(3, 6);
    //     {
    //         let ret_node = parser.get(ret_node_id);
    //         assert_eq!(ret_node.ctrl(), 3);
    //         assert_eq!(ret_node.ctrl(), 3);
    //         assert_eq!(ret_node.expr(), 6);
    //         assert_eq!(ret_node.expr(), 6);
    //     }
    //     {
    //         let ret_node = parser.get(ret_node_id);
    //         assert_eq!(ret_node.ctrl(), 3);
    //         assert_eq!(ret_node.ctrl(), 3);
    //         assert_eq!(ret_node.expr(), 6);
    //         assert_eq!(ret_node.expr(), 6);
    //     }
    // }

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
        let return_node = parser.get(n);
        match return_node {
            Node::ReturnNode { _data } => {
                // control input must be START
                let ctrl_n = return_node.ctrl();
                assert_eq!(ctrl_n, parser._START);
                // data input must be the constant
                let data_n = return_node.expr();
                let constant_node = parser.get(data_n);
                match constant_node {
                    Node::ConstantNode { _data, _value } => {
                        assert_eq!(_data._inputs.len(), 1);
                        assert_eq!(42, *_value);
                        assert_eq!(parser._START, _data._inputs[0]) // START node
                    }
                    _ => assert!(false),
                }
                let start_node = parser.get(ctrl_n);
                match start_node {
                    Node::StartNode { _data } => {
                        assert_eq!(0, _data._inputs.len());
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }
}
