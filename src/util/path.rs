use std::{
    path::{Path, PathBuf},
    str::Utf8Error,
    string::FromUtf8Error,
};

use typed_path::{
    NativePath, NativePathBuf, Utf8NativeEncoding, Utf8NativePath, Utf8NativePathBuf, Utf8UnixPath,
    Utf8UnixPathBuf,
};

// For argp::FromArgs
pub fn native_path(value: &str) -> Result<Utf8NativePathBuf, String> {
    Ok(Utf8NativePathBuf::from(value))
}

/// Checks if the path is valid UTF-8 and returns it as a [`Utf8NativePath`].
#[inline]
pub fn check_path(path: &Path) -> Result<&Utf8NativePath, Utf8Error> {
    Utf8NativePath::from_bytes_path(NativePath::new(path.as_os_str().as_encoded_bytes()))
}

/// Checks if the path is valid UTF-8 and returns it as a [`Utf8NativePathBuf`].
#[inline]
pub fn check_path_buf(path: PathBuf) -> Result<Utf8NativePathBuf, FromUtf8Error> {
    Utf8NativePathBuf::from_bytes_path_buf(NativePathBuf::from(
        path.into_os_string().into_encoded_bytes(),
    ))
}

/// Splits a Windows drive prefix ("C:") off the front of a path. typed-path drops
/// the prefix when converting a native path to Unix encoding, and turns "C:/x"
/// into the drive-relative "C:x" when converting back, so [`NativePathExt`] and
/// [`UnixPathExt`] carry it over by hand. Other platforms have no prefix.
pub fn split_drive_prefix(path: &str) -> Option<(&str, &str)> {
    let bytes = path.as_bytes();
    (cfg!(windows) && bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':')
        .then(|| path.split_at(2))
}

pub trait NativePathExt {
    /// Converts to Unix encoding, keeping a Windows drive prefix ("C:/x").
    fn to_unix(&self) -> Utf8UnixPathBuf;
}

impl NativePathExt for Utf8NativePath {
    fn to_unix(&self) -> Utf8UnixPathBuf {
        match split_drive_prefix(self.as_str()) {
            Some((drive, rest)) => Utf8UnixPathBuf::from(format!(
                "{drive}{}",
                Utf8NativePath::new(rest).with_unix_encoding()
            )),
            None => self.with_unix_encoding(),
        }
    }
}

pub trait UnixPathExt {
    /// Converts to native encoding, restoring a Windows drive prefix kept by
    /// [`NativePathExt::to_unix`].
    fn to_native(&self) -> Utf8NativePathBuf;
}

impl UnixPathExt for Utf8UnixPath {
    fn to_native(&self) -> Utf8NativePathBuf {
        match split_drive_prefix(self.as_str()) {
            Some((drive, rest)) => Utf8NativePathBuf::from(format!(
                "{drive}{}",
                Utf8UnixPath::new(rest).with_encoding::<Utf8NativeEncoding>()
            )),
            None => self.with_encoding(),
        }
    }
}
