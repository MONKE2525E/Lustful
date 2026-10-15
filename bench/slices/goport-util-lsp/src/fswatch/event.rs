//! Go: internal/fswatch/event.go (event kinds and the per-directory event
//! list that coalesces events inside one debounce window).
//!
//! PORT: the backend threads and the debouncer thread share an `eventList`,
//! so Go `el.mu` is a `std::sync::Mutex` over the fields it guards
//! (`EventListLocked`). Go's `*Locked` helpers take that guarded data.

use crate::fswatch::prelude::*;

use std::sync::Mutex;

// Go: event.go:6 EventKind
/// EventKind classifies a filesystem change.
///
/// PORT: Go `type EventKind int` with the consts `EventUpdate` (1) and
/// `EventDelete` (2). The shared contract (map-watch-api U1) makes it an
/// enum with the same values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EventKind {
    Update = 1,
    Delete = 2,
}

impl EventKind {
    // Go: event.go:13 EventKind.String
    // PORT: Go also has a `default: "unknown"` case for other ints. The
    // enum has no other values.
    pub fn string(&self) -> String {
        match self {
            EventKind::Update => "update".to_string(),
            EventKind::Delete => "delete".to_string(),
        }
    }
}

// Go: event.go:25 Event
/// Event describes a single filesystem change.
///
/// PORT: Go also has the unexported field `includedWatchRoot`. Code outside
/// this module builds `Event` literals, so the flag is not a field here:
/// `snapshot_since_locked` returns it beside each event, and only
/// `dirWatch.triggerCallbacks` reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub kind: EventKind,
    pub path: String,
}

// Go: event.go:32 eventEntry
/// eventEntry tracks coalescing state during a debounce batch.
#[derive(Clone, Copy, Debug, Default)]
pub struct EventEntry {
    pub created_seq: u64,
    pub updated_seq: u64,
    pub deleted_seq: u64,
    pub included_watch_root: bool,
}

impl EventEntry {
    // Go: event.go:255 eventEntry.isDeleted
    pub fn is_deleted(&self) -> bool {
        self.deleted_seq > self.created_seq && self.deleted_seq > self.updated_seq
    }

    // Go: event.go:259 eventEntry.kindSince
    pub fn kind_since(&self, start_seq: u64) -> Option<EventKind> {
        if self.deleted_seq > start_seq {
            if self.created_seq > start_seq
                && self.created_seq < self.deleted_seq
                && self.updated_seq < self.deleted_seq
            {
                return None;
            }
            return Some(EventKind::Delete);
        }
        let seq = self.created_seq.max(self.updated_seq);
        if seq > start_seq {
            return Some(EventKind::Update);
        }
        None
    }
}

// Go: event.go:42 eventList


