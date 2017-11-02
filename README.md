## Private Set-Union Cardinality (PSC)


# Description


This project, a collaborative effort between researchers at Georgetown University, Tulane University, and the U.S. Naval Research Lab, introduces a cryptographic protocol for efficiently aggregating a count of unique items across a set of data collectors privately -- that is, without exposing any information other than the count.  Our protocol allows for more secure and useful statistics gathering in privacy-preserving distributed systems such as anonymity networks; for example, it allows operators of anonymity networks such as Tor to securely answer the question: _how many unique users were observed using the distributed service?_ We formally prove the correctness and security of our protocol in the Universally Composable framework against an active adversary that compromises all but one of the aggregation parties. We also show that the protocol provides security against adaptive corruption of the distributed data collectors, which prevents them from being victims of targeted compromise. To ensure _safe_ measurements, we also show how the output can satisfy differential privacy.

We present a proof-of-concept implementation of the private set-union cardinality protocol (PSC) and use it to demonstrate that PSC operates with low computational overhead and reasonable bandwidth. In particular, for reasonable deployment sizes, the protocol run at timescales smaller than the typical measurement period would be and thus is suitable for distributed measurement.


# Paper

Ellis Fenske\*, Akshaya Mani\*, Aaron Johnson, and Micah Sherr. Distributed Measurement with Private Set-Union Cardinality. In ACM Conference on Computer and Communications Security (CCS), November 2017.

(* co-first authors)


# Source Code

[Our implementation of PSC is available here](https://github.com/msherr/psc).  Please note that PSC is in active development, and (like all software) may contain bugs.



# Participants

* Ellis Fenske, Tulane University
* Akshaya Mani, Georgetown University
* [Aaron Johnson](http://www.ohmygodel.com/), U.S. Naval Research Laboratory
* [Micah Sherr](https://security.cs.georgetown.edu/~msherr), Georgetown University

