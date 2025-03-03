# Frontend and backend

The POD2 system consists of a frontend and a backend, connected by a middleware.  This page outlines some design principles for deciding which components go where.

```
user -- frontend -- middleware -- backend -- ZK circuit
```

The frontend is what we want the user to see; the backend is what we want the circuit to see.

## Circuit and proving system

The first implementation of POD2 uses Plonky2 as its proving system.  In principle, a future implementation could use some other proving system.  The frontend and middleware should not be aware of what proving system is in use: anything specific to the proving system belongs to the backend.

## User-facing types versus in-circuit types

The frontend type system exposes human-readable types to POD developers: strings, ints, bools, and so forth.  On the backend, all types are build out of field elements.  The middleware should handle the conversion.
