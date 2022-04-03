use std::fmt::Write as FmtWrite;
use std::io::Write as IoWrite;

/// An Authority manages access to Scopes
pub trait Authority
{
    /// State will be used to initialize scopes
    type State;

    /// calls init() on the scope and returns an initialized scope
    fn scope<T>(&mut self, scope: T) -> T
    where 
        T: Scope<Self::State>;
}

/// Scope accepts and processes messages after being initialized by an authority
pub trait Scope<S> {
    /// Messages processed by this scope
    type Message;

    /// called by the authority to initialize this scope w/ the current state
    fn init(&mut self, init: &S) -> Self;

    /// called with a msg for the scope to process, when ready the scope will respond by writing to data_out and log
    fn notify(&mut self, msg: Self::Message, data_out: impl IoWrite, log: impl FmtWrite) -> Result<(), ScopeErr>;
}

/// Idea of how it could be used...
/// ```
/// let authority: Authority;
/// 
/// let mut scope = authority.scope();
/// let scope = &mut scope;
/// 
/// match scope.notify(Msg::Pull, file, stdout) {
///     Ok(()) => file.Read(),
///     Err(ScopeErr::Closed) => ..., 
///     Err(ScopeErr::Locked) => ...,
///     Err(ScopeErr::Stale) => ..., 
/// }
/// ```
/// elsewhere
/// ```
/// fn notify(..., pull, file, log) {
///     file.Write(...);
/// }
/// 
/// fn notify(..., push, remote, log) {
///     remote.Write(...);
/// }
/// ```
pub enum ScopeErr {
    Closed,
    Locked,
    Stale,
}

