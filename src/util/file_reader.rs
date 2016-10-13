const EOF: char = '\x00';

#[derive(Debug)]
pub struct FileReader {
    file: String,
    pos: usize,
    current: char,
    next: char,
    reached_end: bool,
}

impl FileReader {
    pub fn new(file_contents: &str) -> FileReader {
        let mut fr = FileReader {
            file: file_contents.to_owned(),
            pos: 0,
            current: EOF,
            next: EOF,
            reached_end: false,
        };

        // TODO: this is ugly...
        fr.next = fr.char_at(0);
        fr.bump(1);

        fr
    }

    pub fn current_char(&self) -> char {
        self.current
    }

    pub fn next_char(&self) -> char {
        self.next
    }

    pub fn bump(&mut self, n: usize) {
        for _ in 0..n {
            self.bump_once();
        }
    }

    pub fn current_pos(&self) -> usize {
        // This is necessary because self.pos is actually
        // the position of self.next... so we can just subtract
        // the preceding character, which is self.current.
        self.pos - self.current.len_utf8()
    }

    pub fn get_line_from_pos(&self, pos: usize) -> String {
        if pos < self.pos {
            let (line, _) = self.get_row_col(pos);
            self.file.lines().nth(line).unwrap().to_owned()
        } else {
            "<EOF>".to_string() //TODO: What should I actually do here?
        }
    }

    fn bump_once(&mut self) {
        self.current = self.next;
        self.next = if !self.reached_end {
            self.pos += self.next.len_utf8();
            if self.pos < self.file.len() {
                self.char_at(self.pos)
            } else {
                self.reached_end = true;
                EOF
            }
        } else {
            EOF
        };
    }

    fn char_at(&self, n: usize) -> char {
        self.file[n..].chars().next().unwrap_or(EOF)
    }

    pub fn get_row_col(&self, pos: usize) -> (usize, usize) {
        let mut row = 0;
        let mut col = 0;

        for c in self.file[0..pos].chars() {
            if c == '\n' {
                row += 1;
                col = 0;
            } else {
                col += 1;
            }
        }

        (row, col)
    }
}
