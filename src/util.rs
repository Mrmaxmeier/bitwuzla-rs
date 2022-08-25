use libc::c_void;

pub(crate) fn tmp_file_to_string<F: FnOnce(*mut libc::FILE)>(f: F, limit_length: bool) -> String {
    const MAX_LENGTH: i64 = 2000; // If the text representation of the `Array` exceeds this length, subsitute a placeholder instead
    unsafe {
        let tmpfile: *mut libc::FILE = libc::tmpfile();
        if tmpfile.is_null() {
            panic!("Failed to create a temp file");
        }
        f(tmpfile);
        // Seek to the end of `tmpfile`
        assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
        // Get the length of `tmpfile`
        let length = libc::ftell(tmpfile);
        if length < 0 {
            panic!("ftell() returned a negative value");
        }
        // Seek back to the beginning of `tmpfile`
        assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
        if length > MAX_LENGTH && limit_length {
            libc::fclose(tmpfile);
            "<output too large to display>".to_string()
        } else {
            let mut buffer = Vec::with_capacity(length as usize);
            libc::fread(
                buffer.as_mut_ptr() as *mut c_void,
                1,
                length as usize,
                tmpfile,
            );
            buffer.set_len(length as usize);
            let string = String::from_utf8_unchecked(buffer);
            libc::fclose(tmpfile);
            string
        }
    }
}
