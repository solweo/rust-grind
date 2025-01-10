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









// #[allow(dead_code)]
// mod url_shortener {
//     use std::collections::HashMap;
//     use std::rc::Rc;

//     // fn clean_url(url: &str) -> String {
//     //     let re = regex::Regex::new(r"^(?:https?:\\/\\/)?(?:www\\.)?").unwrap();
//     //     let url = re.replace(url, "").to_string();
//     //     let url = regex::Regex::new(r"[^a-z]+")
//     //         .unwrap()
//     //         .replace_all(&url, "")
//     //         .to_string();
//     //     url.replace('.', "")
//     // }
    
//     // fn generate_id(url: &str) -> String {
//     //     let cleaned_url = clean_url(url).repeat(10);
//     //     let gap = cleaned_url.len() / (cleaned_url.len() / 5);
//     //     let mut result = String::new();
        
//     //     for (i, v) in (gap..cleaned_url.len()).step_by(gap).enumerate() {
//     //         result.push(cleaned_url.chars().nth(v).unwrap());
//     //         if i == 3 {
//     //             break;
//     //         }
//     //     }
//     //     result
//     // }

//     // possible short URLs are actually more It's One, Two, Three OR four lower case characters. So not 26^4 But 26^4 + 26^3 + 26^2 + 26 = 475 254

//     const DOMAIN_NAME: &str = "short.ly";

//     /// Look for more of my solutions on github
//     /// https://github.com/solweo/rust-grind
//     struct UrlShortener {
//         db: DB,
//         counter: u32, // For generating short URLs.
//         len: u8,
//     }

//     impl UrlShortener {
//         pub fn new() -> Self {
//             println!("{}", 26_u32.pow(4) + 26_u32.pow(3) + 26_u32.pow(2) + 26_u32.pow(1));
//             Self {
//                 db: DB::new(),
//                 counter: 0,
//                 len: 0,
//             }
//         }

//         pub fn shorten(&mut self, long_url: &str) -> String {
//             // let generate_short_url = {
//             //     let counter = &mut self.counter;
//             //     || Self::generate_short_url(counter)
//             // };

//             // let short = format!(
//             //     "{DOMAIN_NAME}/{}", 
//             //     String::from_utf8_lossy(
//             //         self.db.entry_or_insert(long_url.to_string(), generate_short_url)
//             //     )
//             // );

//             // println!("long: {long_url}\t short: {}", generate_id(long_url));
//             // let a = 26_u32.pow(4) + 26_u32.pow(3) + 26_u32.pow(2) + 26_u32.pow(1);
//             // let a = 26_u32.pow(4) + 26_u32.pow(3) + 26_u32.pow(2) + 26_u32.pow(1);
//             // let a = 26_u32.pow(4) + 26_u32.pow(3) + 26_u32.pow(2) + 26_u32.pow(1);
//             let a = 26_u32.pow(1);
//             for i in 0..a {
//                 let mut i = i;
//                 let mut len = 1;
//                 let a = Self::gsu(&mut len, i);
//                 println!("sh: {a}");
//             }

//             if let Some(short) = self.db.get_right(long_url) {
//                 return format!(
//                     "{DOMAIN_NAME}/{}", 
//                     String::from_utf8_lossy(short)
//                 );
//             }

//             let id = {
//                 // let counter = &mut self.counter;
//                 // Self::generate_short_url(counter)

//                 let counter = &mut (self.db.db.len() as u32);
//                 if counter > &mut (26_u32.pow(4) - 10) {
//                     println!("counter: {counter}");
//                 }
//                 Self::generate_short_url(counter)
//             };

//             let short = format!(
//                 "{DOMAIN_NAME}/{}", 
//                 String::from_utf8_lossy(
//                     self.db.entry_or_insert(long_url.to_string(), id)
//                 )
//             );

//             if self.counter > 26_u32.pow(4) {
//                 println!("Counter overflow: Ran out of unique short URLs!\tlong: {long_url}\tshort: {short}");
//             }

//             short
//         }

//         pub fn redirect(&self, short_url: &str) -> String {
//             if let Some(stripped) = short_url.strip_prefix(format!("{DOMAIN_NAME}/").as_str()) {
//                 if let Ok(short) = <[u8; 4]>::try_from(stripped.as_bytes()) {
//                     if let Some(long_url) = self.db.get_left(&short) {
//                         if self.counter > 26_u32.pow(4) {
//                             println!("redirect\tshort: {short_url}\tcounter: {}", self.counter)
//                         }
//                         return long_url.to_string();
//                     }
//                 }
//             }
//             "404 Not Found".to_string()
//         }

//         fn gsu(len: &mut u8, counter: u32) -> String {
//             let arr = [0_u8; 4];
//             println!("arr: {}", String::from_utf8_lossy(&arr));



//             // let mut counter = counter + 1 - 26_u32.pow(*len as u32 - 1);
            
//             // let short_url = (1..=*len).map(|_| {
//             //     let c = b'a' + (counter % 26) as u8;
//             //     counter /= 26;
//             //     c
//             // }).collect::<Vec<_>>();
            
//             // let short_url = String::from_utf8_lossy(&short_url).to_string();





//             // self.hash.iter_mut().skip_while(predicate)

//             // let short = (1..4).find(|p| {
//             //     if let Some(i) = 26_u32.pow(*p).checked_sub(self.counter) {
                    
//             //         todo!()
//             //     } else {
//             //         false
//             //     }
//             // });

//             // let short = match self.counter {
//             //     i if i < 26 => {1},
//             //     i if i < 26 + 26_u32.pow(2) => {1},
//             //     i if i < 26 + 26_u32.pow(2) + 26_u32.pow(3) => {1},
//             //     i if i < 26 + 26_u32.pow(2) + 26_u32.pow(3) + 26_u32.pow(4) => {1},
//             // };

//             // let mut value = *counter;
//             // let mut num = (*counter + 1).ilog(26) + 1;

//             // let short_url = [0; 4].map(|_| {
//             //     let c = if num.checked_sub(1).is_some() {
//             //         b'a' + (value % 26) as u8
//             //     } else {
//             //         0
//             //     };
//             //     value /= 26;
//             //     c
//             // });

//             // 100_f64.log(26_f64)

//             // let num = (*counter + 1).ilog(26);
//             // for i in (0..num) {
//             //     short_url[i as usize] += b'a';
//             // }

//             // short_url
//             // *counter += 1;

//             todo!()
//         }

//         /// For some fancy reason, you have to use alphabetical encoding fudge
//         fn generate_short_url(counter: &mut u32) -> ShortUrl {
//             // assert!(*counter < 26_u32.pow(4), "Counter overflow: Ran out of unique short URLs!");
//             let mut value = *counter;

//             let short_url = [b'a'; 4].map(|c| {
//                 let c = c + (value % 26) as u8;
//                 value /= 26;
//                 c
//             });

//             *counter += 1;
//             short_url
//         }
//     }

//     type LongUrl = Rc<str>;
//     type ShortUrl = [u8; 4];

//     /// Naive BiMap implementation for O(1)-ish speed 
//     struct DB {
//         pub db: HashMap<LongUrl, ShortUrl>,
//         rev_db: HashMap<ShortUrl, LongUrl>,
//     }

//     impl DB {
//         pub fn new() -> Self {
//             Self {
//                 db: HashMap::new(),
//                 rev_db: HashMap::new(),
//             }
//         }

//         // pub fn entry_or_insert<F>(&mut self, key: String, default: F) -> &ShortUrl
//         // where
//         //     F: FnOnce() -> ShortUrl,
//         // {
//         //     let key: Rc<str> = Rc::from(key);
//         //     let short_url = self.db.entry(Rc::clone(&key)).or_insert_with(default);
//         //     self.rev_db.entry(*short_url).or_insert(key);
//         //     short_url

//         // }

//         pub fn entry_or_insert(&mut self, key: String, default: ShortUrl) -> &ShortUrl {
//             let key: Rc<str> = Rc::from(key);
//             let short_url = self.db.entry(Rc::clone(&key)).or_insert(default);
//             self.rev_db.entry(*short_url).or_insert(key);
//             short_url

//         }

//         pub fn get_right(&self, key: &str) -> Option<&ShortUrl> {
//             // Look up in `db` using a temporary `Rc<str>` to match keys.
//             self.db.get(&Rc::from(key))
//         }

//         pub fn get_left(&self, key: &ShortUrl) -> Option<&str> {
//             self.rev_db.get(key).map(|rc_str| &**rc_str)
//         }
//     }

//     #[macro_export]
//     macro_rules! assert_valid_short_url {
//         ($url:expr) => {
//             assert!(
//                 $url.starts_with("short.ly/"),
//                 "URL format is incorrect: should start with \"short.ly/\", got: {}",
//                 $url,
//             );
            
//             assert!(
//                 $url.len() < 14,
//                 "URL format is incorrect: length should be < 14 characters, got: {}",
//                 $url,
//             );
            
//             // As the URL contains "short.ly/", we can safely index using [9..]
//             assert!(
//                 $url[9..].bytes().all(|b| b.is_ascii_lowercase()),
//                 "URL format is incorrect: should contain lowercase letters at the end, got: {}",
//                 $url,
//             );
//         }
//     }  

//     #[test]
//     fn two_different_urls() {
//         let mut url_shortener = UrlShortener::new();
        
//         let short_url_1 = url_shortener.shorten("https://www.codewars.com/kata/5ef9ca8b76be6d001d5e1c3e");
//         assert_valid_short_url!(&short_url_1);
        
//         let short_url_2 = url_shortener.shorten("https://www.codewars.com/kata/5efae11e2d12df00331f91a6");
//         assert_valid_short_url!(&short_url_2);
        
//         assert_eq!(url_shortener.redirect(&short_url_1), "https://www.codewars.com/kata/5ef9ca8b76be6d001d5e1c3e");
//         assert_eq!(url_shortener.redirect(&short_url_2), "https://www.codewars.com/kata/5efae11e2d12df00331f91a6");
//     }
    
//     #[test]
//     fn same_urls() {
//         let mut url_shortener = UrlShortener::new();
        
//         let short_url_1 = url_shortener.shorten("https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f");
//         assert_valid_short_url!(&short_url_1);
        
//         let short_url_2 = url_shortener.shorten("https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f");
//         assert_valid_short_url!(&short_url_2);
        
//         assert_eq!(short_url_1, short_url_2, "Should work with the same long URLs");
//         assert_eq!(
//             url_shortener.redirect(&short_url_1),
//             "https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f",
//             "{} should redirect to https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f",
//             &short_url_1,
//         );
//     }
// }





















// #[allow(dead_code)]
// mod url_shortener_two {
//     use std::collections::HashMap;
//     use std::sync::Mutex;
//     use lazy_static::lazy_static;

//     lazy_static! {
//         static ref DB: Mutex<HashMap<String, String>> = Mutex::new(HashMap::new());
//     }

//     fn clean_url(url: &str) -> String {
//         let re = regex::Regex::new(r"^(?:https?:\\/\\/)?(?:www\\.)?").unwrap();
//         let url = re.replace(url, "").to_string();
//         let url = regex::Regex::new(r"[^a-z]+")
//             .unwrap()
//             .replace_all(&url, "")
//             .to_string();
//         url.replace('.', "")
//     }

//     fn generate_id(url: &str) -> String {
//         let cleaned_url = clean_url(url).repeat(10);
//         let gap = cleaned_url.len() / (cleaned_url.len() / 5);
//         let mut result = String::new();
        
//         for (i, v) in (gap..cleaned_url.len()).step_by(gap).enumerate() {
//             result.push(cleaned_url.chars().nth(v).unwrap());
//             if i == 3 {
//                 break;
//             }
//         }
//         result
//     }

//     struct UrlShortener {
//     }

//     impl UrlShortener {
//         pub fn new() -> Self {
//             Self {
//             }
//         }

//         pub fn shorten(&mut self, long_url: &str) -> String {
//             let short_url = format!("short.ly/{}", generate_id(long_url));
//             let mut db = DB.lock().unwrap();
//             db.insert(short_url.clone(), long_url.to_string());
//             short_url
//         }

//         pub fn redirect(&self, short_url: &str) -> String {
//             let db = DB.lock().unwrap();
//             db.get(short_url).cloned().unwrap()
//         }
//     }

//     #[macro_export]
//     macro_rules! assert_valid_short_url {
//         ($url:expr) => {
//             assert!(
//                 $url.starts_with("short.ly/"),
//                 "URL format is incorrect: should start with \"short.ly/\", got: {}",
//                 $url,
//             );
            
//             assert!(
//                 $url.len() < 14,
//                 "URL format is incorrect: length should be < 14 characters, got: {}",
//                 $url,
//             );
            
//             // As the URL contains "short.ly/", we can safely index using [9..]
//             assert!(
//                 $url[9..].bytes().all(|b| b.is_ascii_lowercase()),
//                 "URL format is incorrect: should contain lowercase letters at the end, got: {}",
//                 $url,
//             );
//         }
//     }  

//     #[test]
//     fn two_different_urls() {
//         let mut url_shortener = UrlShortener::new();
        
//         let short_url_1 = url_shortener.shorten("https://www.codewars.com/kata/5ef9ca8b76be6d001d5e1c3e");
//         assert_valid_short_url!(&short_url_1);
        
//         let short_url_2 = url_shortener.shorten("https://www.codewars.com/kata/5efae11e2d12df00331f91a6");
//         assert_valid_short_url!(&short_url_2);
        
//         assert_eq!(url_shortener.redirect(&short_url_1), "https://www.codewars.com/kata/5ef9ca8b76be6d001d5e1c3e");
//         assert_eq!(url_shortener.redirect(&short_url_2), "https://www.codewars.com/kata/5efae11e2d12df00331f91a6");
//     }
    
//     #[test]
//     fn same_urls() {
//         let mut url_shortener = UrlShortener::new();
        
//         let short_url_1 = url_shortener.shorten("https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f");
//         assert_valid_short_url!(&short_url_1);
        
//         let short_url_2 = url_shortener.shorten("https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f");
//         assert_valid_short_url!(&short_url_2);
        
//         assert_eq!(short_url_1, short_url_2, "Should work with the same long URLs");
//         assert_eq!(
//             url_shortener.redirect(&short_url_1),
//             "https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f",
//             "{} should redirect to https://www.codewars.com/kata/5ef9c85dc41b4e000f9a645f",
//             &short_url_1,
//         );
//     }
// }