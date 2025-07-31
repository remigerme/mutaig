use std::{fs::File, io::BufReader, path::Path};

use crate::{Aig, Result, aig::error::ParserError};

fn read_u64(s: &str) -> std::result::Result<u64, ParserError> {
    s.parse::<u64>()
        .map_err(|_| ParserError::InvalidToken(s.to_string() + " expected u64"))
}

fn check_even(x: u64) -> Result<()> {
    if x & 1 == 1 {
        return Err(ParserError::InvalidToken(
            "expected literal to be even, got ".to_string() + &x.to_string(),
        )
        .into());
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Header {
    _m: u64,
    i: u64,
    l: u64,
    o: u64,
    a: u64,
}

impl TryFrom<&String> for Header {
    type Error = ParserError;

    fn try_from(line: &String) -> std::result::Result<Self, Self::Error> {
        let tokens = line.trim().split_whitespace().collect::<Vec<&str>>();

        if tokens.len() < 6 {
            return Err(ParserError::InvalidToken(
                "missing header tokens".to_string(),
            ));
        }

        if tokens[0] != "aag" && tokens[0] != "aig" {
            return Err(ParserError::InvalidToken(
                "expected aag (or at least aig)".to_string(),
            ));
        }

        let m = read_u64(tokens[1])?;
        let i = read_u64(tokens[2])?;
        let l = read_u64(tokens[3])?;
        let o = read_u64(tokens[4])?;
        let a = read_u64(tokens[5])?;

        if tokens.len() > 6 {
            return Err(ParserError::UnsupportedFeature(
                "header only supports M I L O A".to_string(),
            ));
        }

        Ok(Header { _m: m, i, l, o, a })
    }
}

/// Parser for the ASCII AIGER format.
mod ascii {
    use crate::{
        Aig, AigEdge, AigNode, NodeId, Result,
        aig::error::ParserError,
        aig::parser::{Header, check_even, read_u64},
    };
    use std::io::{BufRead, BufReader, Read};

    fn read_input(line: &String) -> Result<NodeId> {
        let tokens = line.trim().split_whitespace().collect::<Vec<&str>>();

        if tokens.len() < 1 {
            return Err(
                ParserError::InvalidToken("expected input token, got nothing".to_string()).into(),
            );
        }

        if tokens.len() > 1 {
            return Err(ParserError::InvalidToken(
                "expected nothing after input, got ".to_string() + tokens[1],
            )
            .into());
        }

        let i = read_u64(tokens[0])?;
        check_even(i)?;
        Ok(i >> 1)
    }

    fn read_inputs(i: u64, reader: &mut BufReader<impl Read>) -> Result<Vec<NodeId>> {
        let mut inputs = Vec::new();
        let mut line = String::new();
        for _ in 0..i {
            reader.read_line(&mut line).unwrap();
            inputs.push(read_input(&line)?);
            line.clear();
        }
        Ok(inputs)
    }

    fn read_latch(line: &String) -> Result<(NodeId, NodeId, bool, Option<bool>)> {
        let tokens = line.trim().split_whitespace().collect::<Vec<&str>>();

        if tokens.len() < 2 {
            return Err(ParserError::InvalidToken("not enough latch tokens".to_string()).into());
        }

        if tokens.len() > 3 {
            return Err(ParserError::InvalidToken(
                "expected nothing after latch, got ".to_string() + tokens[3],
            )
            .into());
        }

        let id = read_u64(tokens[0])?;
        let next = read_u64(tokens[1])?;
        let init = if tokens.len() > 2 {
            let res = read_u64(tokens[2])?;
            if res == 0 {
                Ok(Some(false))
            } else if res == 1 {
                Ok(Some(true))
            } else if res == id {
                Ok(None)
            } else {
                Err(ParserError::InvalidToken(
                    "expected 0 1 or latch id for latch initialization, got ".to_string()
                        + tokens[2],
                ))
            }
        } else {
            Ok(Some(false))
        }?;
        check_even(id)?;
        let next_id = next >> 1;
        let next_compl = next & 1 != 0;
        Ok((id >> 1, next_id, next_compl, init))
    }

    fn read_latches(
        l: u64,
        reader: &mut BufReader<impl Read>,
    ) -> Result<Vec<(NodeId, NodeId, bool, Option<bool>)>> {
        let mut latches = Vec::new();
        let mut line = String::new();
        for _ in 0..l {
            reader.read_line(&mut line).unwrap();
            latches.push(read_latch(&line)?);
            line.clear();
        }
        Ok(latches)
    }

    fn read_output(line: &String) -> Result<(NodeId, bool)> {
        let tokens = line.trim().split_whitespace().collect::<Vec<&str>>();

        if tokens.len() < 1 {
            return Err(ParserError::InvalidToken(
                "expected output token, got nothing".to_string(),
            )
            .into());
        }

        if tokens.len() > 1 {
            return Err(ParserError::InvalidToken(
                "expected nothing after output, got ".to_string() + tokens[1],
            )
            .into());
        }

        let o = read_u64(tokens[0])?;
        let oid = o >> 1;
        let ocomplement = (o & 1) != 0;
        Ok((oid, ocomplement))
    }

    fn read_outputs(o: u64, reader: &mut BufReader<impl Read>) -> Result<Vec<(NodeId, bool)>> {
        let mut outputs = Vec::new();
        let mut line = String::new();
        for _ in 0..o {
            reader.read_line(&mut line).unwrap();
            outputs.push(read_output(&line)?);
            line.clear();
        }
        Ok(outputs)
    }

    fn read_and(line: &String) -> Result<(NodeId, NodeId, bool, NodeId, bool)> {
        let tokens = line.trim().split_whitespace().collect::<Vec<&str>>();

        if tokens.len() < 3 {
            return Err(ParserError::InvalidToken("not enough and tokens".to_string()).into());
        }

        if tokens.len() > 3 {
            return Err(ParserError::InvalidToken(
                "expected nothing after and tokens, got ".to_string() + tokens[3],
            )
            .into());
        }

        let id = read_u64(tokens[0])?;
        let fanin0 = read_u64(tokens[1])?;
        let fanin1 = read_u64(tokens[2])?;

        check_even(id)?;
        let fanin0_id = fanin0 >> 1;
        let fanin0_complement = (fanin0 & 1) != 0;
        let fanin1_id = fanin1 >> 1;
        let fanin1_complement = (fanin1 & 1) != 0;
        Ok((
            id >> 1,
            fanin0_id,
            fanin0_complement,
            fanin1_id,
            fanin1_complement,
        ))
    }

    fn read_ands(
        a: u64,
        reader: &mut BufReader<impl Read>,
    ) -> Result<Vec<(NodeId, NodeId, bool, NodeId, bool)>> {
        let mut ands = Vec::new();
        let mut line = String::new();
        for _ in 0..a {
            reader.read_line(&mut line).unwrap();
            ands.push(read_and(&line)?);
            line.clear();
        }
        Ok(ands)
    }

    /// Builder for the AIGER format.
    fn build_aig(
        inputs: Vec<NodeId>,
        latches: Vec<(NodeId, NodeId, bool, Option<bool>)>,
        outputs: Vec<(NodeId, bool)>,
        ands: Vec<(NodeId, NodeId, bool, NodeId, bool)>,
    ) -> Result<Aig> {
        let mut aig = Aig::new();

        // First, the constant node false
        let node_false = aig.add_node(AigNode::False).unwrap();

        // Starting by inputs
        for &id in &inputs {
            aig.add_node(AigNode::Input(id))?;
        }

        // Adding latches
        // First step: add and nodes with dummy edges to node false
        for &(id, _, _, init) in &latches {
            aig.add_node(AigNode::latch(
                id,
                AigEdge::new(node_false.clone(), false),
                init,
            ))?;
        }

        // Adding and gates
        // First step: add and nodes with dummy edges to node false
        for &(id, _, _, _, _) in &ands {
            aig.add_node(AigNode::and(
                id,
                AigEdge::new(node_false.clone(), false),
                AigEdge::new(node_false.clone(), false),
            ))?;
        }
        // Then replace with real edges
        for &(id, fanin0_id, fanin0_complement, fanin1_id, fanin1_complement) in &ands {
            aig.replace_fanin(id, crate::FaninId::Fanin0, fanin0_id, fanin0_complement)?;
            aig.replace_fanin(id, crate::FaninId::Fanin1, fanin1_id, fanin1_complement)?;
        }

        // Edit the fanin of the latches
        for &(id, next_id, next_compl, _) in &latches {
            aig.replace_fanin(id, crate::FaninId::Fanin0, next_id, next_compl)?;
        }

        // And finally marking outputs
        for &(id, compl) in &outputs {
            // We don't want to mark constant node or inputs as output.
            if id >= 1 + inputs.len() as u64 {
                aig.add_output(id, compl)?;
            }
        }

        // Let's clean the useless stuff
        aig.update();

        // Is the AIG okay?
        aig.check_integrity()?;

        Ok(aig)
    }

    impl Aig {
        /// Creates an AIG from an open .aag file using ASCII format.
        ///
        /// Use this function if the file is already open with the reader.
        pub fn from_ascii(mut reader: BufReader<impl Read>) -> Result<Self> {
            let mut line: String = String::new();

            // Reading the header
            reader.read_line(&mut line).unwrap();
            let header: Header = Header::try_from(&line)?;
            line.clear();

            // Reading inputs, latches, outputs and and gates
            // Ignoring everything else
            let inputs = read_inputs(header.i, &mut reader)?;
            let latches = read_latches(header.l, &mut reader)?;
            let outputs = read_outputs(header.o, &mut reader)?;
            let ands = read_ands(header.a, &mut reader)?;

            build_aig(inputs, latches, outputs, ands)
        }
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn read_input_test() {
            assert!(read_input(&"".to_string()).is_err());
            assert!(read_input(&" ".to_string()).is_err());
            assert!(read_input(&"-5".to_string()).is_err());
            assert!(read_input(&"2 14".to_string()).is_err());
            assert!(read_input(&"4 z".to_string()).is_err());
            assert!(read_input(&"3".to_string()).is_err());

            assert_eq!(read_input(&" 2".to_string()).unwrap(), 1);
            assert_eq!(read_input(&"2 ".to_string()).unwrap(), 1);
            assert_eq!(read_input(&"   42  ".to_string()).unwrap(), 21);
            assert_eq!(read_input(&"0".to_string()).unwrap(), 0);
        }

        #[test]
        fn read_output_test() {
            assert!(read_output(&"".to_string()).is_err());
            assert!(read_output(&" ".to_string()).is_err());
            assert!(read_output(&"-5".to_string()).is_err());
            assert!(read_output(&"2 14".to_string()).is_err());
            assert!(read_output(&"4 z".to_string()).is_err());

            assert_eq!(read_output(&" 2".to_string()).unwrap(), (1, false));
            assert_eq!(read_output(&"3 ".to_string()).unwrap(), (1, true));
            assert_eq!(read_output(&"   42  ".to_string()).unwrap(), (21, false));
            assert_eq!(read_output(&"0".to_string()).unwrap(), (0, false));
        }

        #[test]
        fn read_and_test() {
            assert!(read_and(&"".to_string()).is_err());
            assert!(read_and(&" ".to_string()).is_err());
            assert!(read_and(&"-5".to_string()).is_err());
            assert!(read_and(&"2 14".to_string()).is_err());
            assert!(read_and(&"4 18 2 2".to_string()).is_err());
            assert!(read_and(&"3 2 1".to_string()).is_err());

            assert_eq!(
                read_and(&"2 6 7".to_string()).unwrap(),
                (1, 3, false, 3, true)
            );
            assert_eq!(
                read_and(&"6 0 18".to_string()).unwrap(),
                (3, 0, false, 9, false)
            );
            assert_eq!(
                read_and(&"   42   5 19   ".to_string()).unwrap(),
                (21, 2, true, 9, true)
            );
        }

        #[test]
        fn read_latch_test() {
            assert!(read_latch(&"".to_string()).is_err());
            assert!(read_latch(&" ".to_string()).is_err());
            assert!(read_latch(&"-5".to_string()).is_err());
            assert!(read_latch(&"3 14".to_string()).is_err());
            assert!(read_latch(&"4 18 2".to_string()).is_err());
            assert!(read_latch(&"3 2 1".to_string()).is_err());

            assert_eq!(
                read_latch(&"2 6".to_string()).unwrap(),
                (1, 3, false, Some(false))
            );
            assert_eq!(
                read_latch(&"6 1 1".to_string()).unwrap(),
                (3, 0, true, Some(true))
            );
            assert_eq!(
                read_latch(&"6 1 0".to_string()).unwrap(),
                (3, 0, true, Some(false))
            );
            assert_eq!(
                read_latch(&"6 1 6".to_string()).unwrap(),
                (3, 0, true, None)
            );
        }
    }
}

/// Parser for the bin AIGER format.
mod bin {
    use std::io::{BufRead, BufReader, Read};

    use crate::{
        Aig, AigEdge, AigError, AigNode, NodeId, Result,
        aig::error::ParserError,
        aig::parser::{Header, read_u64},
    };

    fn read_and_partially_register_latch(
        aig: &mut Aig,
        lvar: u64,
        header: Header,
        line: &String,
    ) -> Result<(NodeId, NodeId, bool)> {
        let tokens = line.trim().split_whitespace().collect::<Vec<&str>>();

        if tokens.len() < 1 {
            return Err(ParserError::InvalidToken("not enough latch tokens".to_string()).into());
        }

        if tokens.len() > 2 {
            return Err(ParserError::InvalidToken(
                "expected nothing after latch, got ".to_string() + tokens[3],
            )
            .into());
        }

        let id = header.i + lvar + 1;
        let next = read_u64(tokens[0])?;
        let next_id = next >> 1;
        let next_compl = next & 1 != 0;

        let init = if tokens.len() > 1 {
            let res = read_u64(tokens[1])?;
            if res == 0 {
                Ok(Some(false))
            } else if res == 1 {
                Ok(Some(true))
            } else if res == (id << 1) {
                Ok(None)
            } else {
                eprintln!("{}, {}", res, id);
                Err(ParserError::InvalidToken(
                    "expected 0 1 or latch id for latch initialization, got ".to_string()
                        + tokens[1],
                ))
            }
        } else {
            Ok(Some(false))
        }?;

        // Partially registering latch with a dummy fanin
        let dummy = aig.get_node(0).unwrap();
        aig.add_node(AigNode::latch(id, AigEdge::new(dummy, false), init))?;

        // Returning the fanin information for later
        Ok((id, next_id, next_compl))
    }

    fn read_and_partially_register_latches(
        aig: &mut Aig,
        reader: &mut BufReader<impl Read>,
        header: Header,
    ) -> Result<Vec<(NodeId, NodeId, bool)>> {
        let mut latches = Vec::new();
        let mut line = String::new();

        for lvar in 0..header.l {
            reader.read_line(&mut line).unwrap();
            latches.push(read_and_partially_register_latch(aig, lvar, header, &line)?);
            line.clear();
        }
        Ok(latches)
    }

    fn read_output(line: &String) -> Result<(NodeId, bool)> {
        let tokens = line.trim().split_whitespace().collect::<Vec<&str>>();

        if tokens.len() < 1 {
            return Err(ParserError::InvalidToken(
                "expected output token, got nothing".to_string(),
            )
            .into());
        }

        if tokens.len() > 1 {
            return Err(ParserError::InvalidToken(
                "expected nothing after output, got ".to_string() + tokens[1],
            )
            .into());
        }

        let o = read_u64(tokens[0])?;
        let oid = o >> 1;
        let ocomplement = (o & 1) != 0;
        Ok((oid, ocomplement))
    }

    fn read_outputs(
        reader: &mut BufReader<impl Read>,
        header: Header,
    ) -> Result<Vec<(NodeId, bool)>> {
        let mut outputs = Vec::new();
        let mut line = String::new();

        for _ in 0..header.o {
            reader.read_line(&mut line).unwrap();
            outputs.push(read_output(&line)?);
            line.clear();
        }
        Ok(outputs)
    }

    fn getnoneofch(buf: &[u8], offset: &mut usize) -> Result<u8> {
        if *offset >= buf.len() {
            return Err(ParserError::InvalidToken("unexpected end of file".to_string()).into());
        }

        let byte = buf[*offset];
        *offset += 1;
        Ok(byte)
    }

    fn decode_delta(buf: &[u8], offset: &mut usize) -> Result<u64> {
        let mut x = 0;
        let mut i = 0;

        while let Ok(ch) = getnoneofch(buf, offset) {
            x |= ((ch & 0x7f) as u64) << (7 * i);
            i += 1;

            if ch & 0x80 == 0 {
                break;
            }
        }
        Ok(x)
    }

    fn read_and_register_ands(
        aig: &mut Aig,
        reader: &mut BufReader<impl Read>,
        header: Header,
    ) -> Result<()> {
        let mut buf = Vec::new();
        reader.read_to_end(&mut buf).unwrap();

        let mut offset = 0;
        let mut lhs = 2 * (header.i + header.l + 1);

        for _ in 0..header.a {
            let delta0 = decode_delta(&buf, &mut offset)?;
            let delta1 = decode_delta(&buf, &mut offset)?;

            let rhs0 = lhs - delta0;
            let rhs1 = rhs0 - delta1;

            aig.add_node(AigNode::and(
                lhs >> 1,
                AigEdge::new(
                    aig.get_node(rhs0 >> 1)
                        .ok_or(AigError::NodeDoesNotExist(rhs0 >> 1))?,
                    rhs0 & 1 != 0,
                ),
                AigEdge::new(
                    aig.get_node(rhs1 >> 1)
                        .ok_or(AigError::NodeDoesNotExist(rhs1 >> 1))?,
                    rhs1 & 1 != 0,
                ),
            ))?;

            lhs += 2;
        }

        Ok(())
    }

    impl Aig {
        pub fn from_bin(mut reader: BufReader<impl Read>) -> Result<Self> {
            let mut line: String = String::new();

            // Reading the header
            reader.read_line(&mut line).unwrap();
            let header: Header = Header::try_from(&line)?;
            line.clear();

            // Using the binary AIGER format, the AIGER can be built progressively.
            // False node included by the ctor.
            let mut aig = Aig::new();

            // Adding inputs
            for i in 1..1 + header.i {
                aig.add_node(AigNode::Input(i))?;
            }

            // Register latches and collecting their fanin
            let latches = read_and_partially_register_latches(&mut aig, &mut reader, header)?;

            // Collecting outputs for later
            let outputs = read_outputs(&mut reader, header)?;

            // Register and gates
            read_and_register_ands(&mut aig, &mut reader, header)?;

            // Edit the fanin of the latches
            for &(id, next_id, next_compl) in &latches {
                aig.replace_fanin(id, crate::FaninId::Fanin0, next_id, next_compl)?;
            }

            // And finally marking outputs
            for &(id, compl) in &outputs {
                // We don't want to mark the constant node or an input as an output
                // this is obviously true as these won't be modified anyway
                if id >= 1 + header.i {
                    aig.add_output(id, compl)?;
                }
            }

            // Let's clean the useless stuff
            aig.update();

            // Is the AIG okay?
            aig.check_integrity()?;

            Ok(aig)
        }
    }
}

impl Aig {
    /// Creates an AIG from an .aig (resp .aag) file using bin (resp. ASCII) AIGER format.
    ///
    /// Warning, this uses a homemade "parser" which isn't super well tested and
    /// definitely does not support all AIG features (only the bare minimum).
    /// We're not trying to open weird looking AIG files or do any sequential work for now.
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let f = File::open(path.as_ref()).map_err(|z| ParserError::IoError(z.to_string()))?;
        let reader = BufReader::new(f);
        match path.as_ref().extension().and_then(|ext| ext.to_str()) {
            Some("aag") => Aig::from_ascii(reader),
            Some("aig") => Aig::from_bin(reader),
            _ => Err(
                ParserError::IoError("invalid extension, expected .aag or .aig".to_string()).into(),
            ),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn read_u64_test() {
        assert!(read_u64("").is_err());
        assert!(read_u64(" ").is_err());
        assert!(read_u64(" 2").is_err());
        assert!(read_u64("2 ").is_err());
        assert!(read_u64("-5").is_err());

        assert_eq!(read_u64("42").unwrap(), 42);
        assert_eq!(read_u64("0").unwrap(), 0);
    }

    #[test]
    fn header_try_from_test() {
        assert!(Header::try_from(&"".to_string()).is_err());
        assert!(Header::try_from(&"aag 0 0 0 0".to_string()).is_err());

        let h_empty = Header {
            _m: 0,
            i: 0,
            l: 0,
            o: 0,
            a: 0,
        };

        assert_eq!(
            Header::try_from(&"   aag 0 0 0 0 0 ".to_string()).unwrap(),
            h_empty
        );

        // In theory, this shouldn't work but a lot of people do not care about aig vs aag
        // cf the official benchmarks
        assert_eq!(
            Header::try_from(&"aig 0 0 0 0 0".to_string()).unwrap(),
            h_empty
        );

        assert_eq!(
            Header::try_from(&"aag 1 18 2 0 1     ".to_string()).unwrap(),
            Header {
                _m: 1,
                i: 18,
                l: 2,
                o: 0,
                a: 1
            }
        );

        assert!(Header::try_from(&"aag 1 1 -1 1 1".to_string()).is_err());
    }
}
