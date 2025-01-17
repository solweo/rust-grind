/// -*- coding:utf-8 -*-
/// title       : ■□ Pattern □■ : Zoom
/// kata UUID   : 56e6705b715e72fef0000647
/// tags        : ['ASCII Art', 'Puzzles']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod pattern_zoom {
    use itertools::Itertools;
    use std::cmp::max;

    fn zoom(n: i32) -> String {
        const EMPTY: char = '□';
        const FILLED: char = '■';

        let rule = |x: i32, y: i32| max(
            x.abs_diff(n/2), 
            y.abs_diff(n/2)) % 2 == 0;
        
        (0..n).map(|row| (0..n).map(|column| 
            match rule(row, column) {
                true => FILLED,
                false => EMPTY,
            })
            .join(""))
            .join("\n")
    }

    #[test]
    fn basic_test_1() {
    assert_eq!(zoom(1), "■");
    }

    #[test]
    fn basic_test_2() {
    assert_eq!(zoom(3), "\
□□□
□■□
□□□"
    );
    }

    #[test]
    fn basic_test_3() {
    assert_eq!(zoom(5), "\
■■■■■
■□□□■
■□■□■
■□□□■
■■■■■"
    );
    }

    #[test]
    fn basic_test_4() {
    assert_eq!(zoom(7), "\
□□□□□□□
□■■■■■□
□■□□□■□
□■□■□■□
□■□□□■□
□■■■■■□
□□□□□□□"
    );
    }

    #[test]
    fn basic_test_5() {
    assert_eq!(zoom(9), "\
■■■■■■■■■
■□□□□□□□■
■□■■■■■□■
■□■□□□■□■
■□■□■□■□■
■□■□□□■□■
■□■■■■■□■
■□□□□□□□■
■■■■■■■■■"
    );
    }
}

/// -*- coding:utf-8 -*-
/// title       : Find the smallest
/// kata UUID   : 573992c724fc289553000e95
/// tags        : ['Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod find_the_smallest {
    use itertools::Itertools;
    use std::cmp::Ordering;
    
    /// Solution without Brute-force
    fn smallest(n: i64) -> (i64, usize, usize) {
        let n = digits(n);

        // Regardless of the answer, the location of the change will be identical in all scenarios
        let place_of_change = n.iter().zip(n.iter().sorted())
            .position(|(original, shifted)| original != shifted)
            .unwrap_or(0);

        // But the thing is, we can't really tell whether the value was taken from that place or placed upon it
        // Therefore, it is vital to check both scenarios
        let try_from_right = n[place_of_change+1..]
            .iter()
            .rev()
            .tuple_windows()
            .scan(n.len()-1, |state, (&a, &b)|{
                if a == *n[place_of_change+1..].iter().min().unwrap() && a != b {
                    None
                } else {
                    *state -= 1;
                    Some(*state)
                }
            }).last().unwrap_or(n.len()-1);

        let try_to_right = n[place_of_change+1..]
            .iter()
            .tuple_windows()
            .scan(place_of_change+1, |state, (_, &b)|{
                if b > n[place_of_change] {
                    None
                } else {
                    *state += 1;
                    Some(*state)
                }
            }).last().unwrap_or(place_of_change+1);

        // There is an chance of getting a raw of exect same digits which sadly aren't ancounetred
        let try_to_right = n[place_of_change+1..=try_to_right].iter()
            .rposition(|&digit| digit != n[place_of_change])
            .map_or(try_to_right, |pos| place_of_change + 1 + pos);
        let place_of_change = n[0..place_of_change].iter()
            .position(|&digit| digit == n[try_from_right])
            .unwrap_or(place_of_change);

        // Generate possible moves and evaluate them
        let moves = [
            move_digit(&mut n.clone(), try_from_right, place_of_change),
            move_digit(&mut n.clone(), place_of_change, try_to_right),
        ];

        // Return the smallest result
        *moves
            .iter()
            .min_by(|&(num1, i1, j1), &(num2, i2, j2)| {
                match num1.cmp(num2) {
                    Ordering::Equal => match i1.cmp(i2) {
                        Ordering::Equal => j1.cmp(j2),
                        x => x,
                    },
                    x => x,
                }
            }) 
            .unwrap()
    }

    fn digits(n: i64) -> Vec<u8> {
        let mut digits = std::iter::repeat(())
            .scan(n, |i, _dummy_value| {
                if *i > 0 {
                    let digit = (*i % 10) as u8;
                    *i /= 10;
                    Some(digit)
                } else {
                    None
                }
            }).collect::<Vec<_>>();

        digits.reverse();
        digits
    }
    
    fn from_digits(digits: &[u8]) -> i64 {
        digits.iter().fold(0i64, |acc, &digit| acc * 10 + digit as i64)
    }
    
    fn move_digit(digits: &mut Vec<u8>, i: usize, j: usize) -> (i64, usize, usize) {
        if i != j {
            let digit = digits.remove(i);
            digits.insert(j, digit);
        }

        (from_digits(digits), i, j)
    }

    fn testing(n: i64, exp: (i64, usize, usize)) {
        let ans = smallest(n);
        assert_eq!(ans, exp, "Testing: {}", n);
    }

    #[test]
    fn basic_tests() {
        testing(209917, (29917, 0, 1));
        testing(269045, (26945, 3, 0));  
        testing(285365, (238565, 3, 1)); 
        testing(261235, (126235, 2, 0));
        testing(219957, (129957, 0, 1));
        testing(935855753, (358557539, 0, 8)); 
        testing(199819884756, (119989884756, 4, 0)); 
        testing(11199819884756, (11119989884756, 6, 0));  
        testing(223399839884756, (223339989884756, 7, 2));  
        testing(29979573762081003, (2997957376208103, 14, 0)); 
        testing(524496252664355423, (244596252664355423, 0, 3)); 
        testing(755566437707740963, (75556643770774963, 14, 0));  
        testing(905537475245977679, (55374752459776799, 0, 16));       
        testing(404701664395569970, (40470166439556997, 17, 0));
        testing(901246778163629482, (12467781636294829, 0, 17));
        testing(603613412202040716, (36134122020406716, 0, 14));
        testing(837687834358978897, (376878343588978897, 0, 10));
    }
}

/// -*- coding:utf-8 -*-
/// title       : Molecule to atoms
/// kata UUID   : 52f831fa9d332c6591000511
/// tags        : ['Parsing', 'Algorithms', 'Strings']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod molecule_to_atoms {
    use std::collections::HashMap;
    use itertools::Itertools;
    use thiserror::Error;

    pub type Atom = (String, usize);
    pub type Molecule = Vec<Atom>;

    #[derive(Error, Debug)]
    pub enum ParseError { 
        #[error("Not a valid molecule")]
        Invalid,
        #[error("Mismatched parenthesis")]
        Mismatch,
    }

    pub fn parse_molecule(s: &str) -> Result<Molecule, ParseError> {
        let mut chars = s.chars().peekable();
        let mut bracket_stack = Vec::new();

        let group_counts = recurs_molecule(&mut chars, 1, &mut bracket_stack)?;
        if !bracket_stack.is_empty() {
            return Err(ParseError::Mismatch);
        }
        
        let molecule = group_counts
            .into_iter()
            .sorted_by(|a, b| a.0.cmp(&b.0))
            .collect::<Molecule>();
        
        Ok(molecule)
    }
    
    fn recurs_molecule<I>(
        chars: &mut std::iter::Peekable<I>,
        multiplier: usize,
        bracket_stack: &mut Vec<char>, 
    ) -> Result<HashMap<String, usize>, ParseError>
    where
        I: Iterator<Item = char>,
    {
        let mut counts = HashMap::new();

        let is_matching_bracket = |open, close| matches!((open, close), ('(', ')') | ('[', ']') | ('{', '}'));
    
        while let Some(&c) = chars.peek() {
            match c {
                c if c.is_uppercase() => {
                    let (element, count) = parse_element(chars)?;
                    *counts.entry(element).or_insert(0) += count * multiplier;
                }
                '(' | '[' | '{' => {
                    chars.next(); // Consume opening bracket
                    bracket_stack.push(c);
                    
                    let inner_atoms = recurs_molecule(chars, 1, bracket_stack)?;
                    let inner_multiplier = parse_multiplier(chars)?;
                    
                    for (element, count) in inner_atoms {
                        *counts.entry(element).or_insert(0) += count * inner_multiplier * multiplier;
                    }
                }
                ')' | ']' | '}' => {
                    chars.next(); // Consume closing bracket
                    if bracket_stack.pop().is_some_and(|open| !is_matching_bracket(open, c)) {
                        return Err(ParseError::Mismatch);
                    }
                    break;
                }
                _ => return Err(ParseError::Invalid),
            }
        }
    
        Ok(counts)
    }
    
    fn parse_element<I>(
        chars: &mut std::iter::Peekable<I>,
    ) -> Result<Atom, ParseError>
    where
        I: Iterator<Item = char>,
    {
        let mut element = String::new();
        element.push(chars.next().ok_or(ParseError::Invalid)?);
    
        if let Some(&c) = chars.peek() {
            if c.is_lowercase() {
                element.push(chars.next().unwrap());
            }
        }
    
        let count = parse_multiplier(chars)?;

        Ok((element, count))
    }
    
    fn parse_multiplier<I>(
        chars: &mut std::iter::Peekable<I>,
    ) -> Result<usize, ParseError>
    where
        I: Iterator<Item = char>,
    {
        let mut multiplier = 0;
    
        while let Some(&c) = chars.peek() {
            if c.is_ascii_digit() {
                multiplier = multiplier * 10 + chars.next().unwrap().to_digit(10).unwrap() as usize;
            } else {
                break;
            }
        }
    
        Ok(if multiplier == 0 { 1 } else { multiplier })
    }

    macro_rules! assert_parse {
        ($formula:expr, $expected:expr, $name:ident) => {
            #[test]
            fn $name() {
                super::assert_parse($formula, &$expected, "");
            }
        }
    }

    mod molecules {
        assert_parse!("H", [("H",1)], hydrogen);
        assert_parse!("O2", [("O",2)], oxygen);
        assert_parse!("H2O", [("H",2),("O",1)], water);
        assert_parse!("Mg(OH)2", [("Mg",1),("O",2),("H",2)], magnesium_hydroxide);
        assert_parse!("K4[ON(SO3)2]2", [("K",4),("O",14),("N",2),("S",4)], fremys_salt);
    }

    #[test]
    fn errors() {
        assert_fail("pie", "Not a valid molecule");
        assert_fail("Mg(OH", "Mismatched parenthesis");
        assert_fail("Mg(OH}2", "Mismatched parenthesis");
    }

    fn assert_fail(formula: &str, msg: &str) {
        let result = parse_molecule(formula);
        assert!(result.is_err(), "expected {} {:?} to fail, got {:?}", msg, formula, result.unwrap());
    }

    fn assert_parse(formula: &str, expected: &[(&str, usize)], _mst: &str) {
        let mut expected = expected.iter()
        .map(|&(name, usize)| (name.to_owned(), usize))
        .collect::<Molecule>();
        let result = parse_molecule(formula);
        assert!(result.is_ok(), "expected {:?} to pass, got {:?}", formula, result);
        let mut actual = result.unwrap();
        actual.sort();
        expected.sort();
        assert_eq!(actual, expected);
    }
}

/// -*- coding:utf-8 -*-
/// title       : URL shortener
/// kata UUID   : 5fee4559135609002c1a1841
/// tags        : ['Databases', 'Algorithms', 'Data Structures']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod url_shortener {
    use std::collections::HashMap;
    use std::rc::Rc;

    const DOMAIN_NAME: &str = "short.ly";

    struct UrlShortener {
        db: DB
    }

    impl UrlShortener {
        pub fn new() -> Self {
            Self {
                db: DB::new()
            }
        }

        pub fn shorten(&mut self, long_url: &str) -> String {
            format!(
                "{DOMAIN_NAME}/{}", 
                self.db.entry_or_insert(long_url)
            )
        }

        pub fn redirect(&self, short_url: &str) -> String {
            if let Some(stripped) = short_url.strip_prefix(format!("{DOMAIN_NAME}/").as_str()) {
                if let Some(long_url) = self.db.get_long(stripped) {
                    return long_url.to_string();
                }
            }
            "404 Not Found".to_string()
        }
    }

    type LongUrl<'a> = &'a str;
    type ShortUrl<'a> = &'a str;

    /// Naive BiMap implementation for O(1)-ish speed 
    struct DB {
        long_to_short: HashMap<Rc<str>, Rc<str>>,
        short_to_long: HashMap<Rc<str>, Rc<str>>,
        /// For some fancy reason, you have to use alphabetical encoding fudge
        pub next_id: Box<dyn FnMut() -> Rc<str>>,
    }

    impl DB {
        pub fn new() -> Self {
            Self {
                long_to_short: HashMap::new(),
                short_to_long: HashMap::new(),
                next_id: {
                    let mut hash_gen = std::iter::successors(Some((1, 0)), |&(len, counter)| {
                        if len > 4 {
                            None
                        } else if counter < 26_i32.pow(len as u32) - 1 {
                            Some((len, counter + 1))
                        } else {
                            Some((len + 1, 0))
                        }
                    });
                    Box::new(move || {
                        let (mut len, mut counter) = hash_gen.next().expect("Counter overflow: Ran out of unique short URLs!");
                        
                        let hash = [b'a'; 4].map(|c| {
                            let c = if len > 0 {
                                len -= 1;
                                c + (counter % 26) as u8
                            } else {
                                b' '
                            };
                            
                            counter /= 26;
                            c
                        });

                        Rc::from(String::from_utf8_lossy(&hash).trim_end())
                    })
                },
            }
        }

        pub fn entry_or_insert(&mut self, key: &str) -> ShortUrl {
            let key: Rc<str> = Rc::from(key);
            let short_url = self.long_to_short
                .entry(Rc::clone(&key))
                .or_insert_with(|| (self.next_id)());
            self.short_to_long
                .entry(short_url.clone())
                .or_insert(key);
            short_url

        }

        pub fn get_short(&self, key: LongUrl) -> Option<ShortUrl> {
            self.long_to_short
                .get(&Rc::from(key))
                .map(|rc_str| &**rc_str)
        }

        pub fn get_long(&self, key: ShortUrl) -> Option<LongUrl> {
            self.short_to_long
                .get(&Rc::from(key))
                .map(|rc_str| &**rc_str)
        }
    }

    #[macro_export]
    macro_rules! assert_valid_short_url {
        ($url:expr) => {
            assert!(
                $url.starts_with("short.ly/"),
                "URL format is incorrect: should start with \"short.ly/\", got: {}",
                $url,
            );
            
            assert!(
                $url.len() < 14,
                "URL format is incorrect: length should be < 14 characters, got: {}",
                $url,
            );
            
            // As the URL contains "short.ly/", we can safely index using [9..]
            assert!(
                $url[9..].bytes().all(|b| b.is_ascii_lowercase()),
                "URL format is incorrect: should contain lowercase letters at the end, got: {}",
                $url,
            );
        }
    }  

    #[test]
    fn two_different_urls() {
        let mut url_shortener = UrlShortener::new();
        
        let short_url_1 = url_shortener.shorten("https://www.codewars.com/kata/5ef9ca8b76be6d001d5e1c3e");
        assert_valid_short_url!(&short_url_1);
        
        let short_url_2 = url_shortener.shorten("https://www.codewars.com/kata/5efae11e2d12df00331f91a6");
        assert_valid_short_url!(&short_url_2);
        
        assert_eq!(url_shortener.redirect(&short_url_1), "https://www.codewars.com/kata/5ef9ca8b76be6d001d5e1c3e");
        assert_eq!(url_shortener.redirect(&short_url_2), "https://www.codewars.com/kata/5efae11e2d12df00331f91a6");
    }
    
    #[test]
    fn same_urls() {
        let mut url_shortener = UrlShortener::new();
        
        let short_url_1 = url_shortener.shorten("https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f");
        assert_valid_short_url!(&short_url_1);
        
        let short_url_2 = url_shortener.shorten("https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f");
        assert_valid_short_url!(&short_url_2);
        
        assert_eq!(short_url_1, short_url_2, "Should work with the same long URLs");
        assert_eq!(
            url_shortener.redirect(&short_url_1),
            "https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f",
            "{} should redirect to https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f",
            &short_url_1,
        );
    }
}