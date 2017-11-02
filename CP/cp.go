/*
Created on Apr 18, 2017

@author: Akshaya Mani, Georgetown University
*/

package main

import (
    "bytes"
    "crypto/tls"
    "crypto/x509"
    "encoding/binary"
    "errors"
    "fmt"
    "github.com/danieldk/par"
    "github.com/dedis/crypto/abstract"
    "github.com/dedis/crypto/hash"
    "github.com/dedis/crypto/nist"
    "github.com/dedis/crypto/shuffle"
    "github.com/dedis/crypto/proof"
    "github.com/dedis/crypto/sign"
    "github.com/golang/protobuf/proto"
    "github.com/dedis/crypto/random"
    "io"
    "io/ioutil"
    "math"
    "math/rand"
    "net"
    "os"
    "psc/DP/dpres"
    "psc/CP/schnorr/schnorrkey"
    "psc/CP/cpres"
    "strconv"
    "syscall"
    "time"
)

// ReRandomizeProof represents a NIZK proof.
type ReRandomizeProof struct {
    C abstract.Scalar //Challenge
    R1 abstract.Scalar //Response 1
    R2 abstract.Scalar //Response 2
    T1 abstract.Point  // public commitment with respect to base point A
    T2 abstract.Point  // public commitment with respect to base point B
}

func main() {
    seed := rand.NewSource(time.Now().UnixNano())
    rnd := rand.New(seed)

    no_CPs := 5 //No.of CPs
    no_DPs := 20 //No. of DPs

    cp_no, port := parseCommandline(os.Args) //Parse CP number, port no.

    b := 200000 //No of entries in IP table
    var agg int64 //Aggregate
    agg = 0

    k_j := make([]abstract.Scalar, b) //Key Share
    c_j := make([]abstract.Scalar, b) //Message Share
    b_j := make([][]byte, no_CPs - 1) //Broadcasted Message List
    r := make([]abstract.Point, b) //List of Elgamal Blinding Factors
    c := make([]abstract.Point, b) //List of Elgamal Ciphers
    y := make([]abstract.Point, no_CPs) //Public Key List
    epsilon := 0.3 //Epsilon
    delta := math.Pow(10, -12) //Delta
    n := int(math.Floor((math.Log(2 / delta) * 64)/math.Pow(epsilon, 2))) + 1 //No. of Noise vectors
    dp_no := 0 //No. of DPs Responded so far
    m_flag := false //Message Flag
    var step_no uint32 //Step Number
    var b_flag bool //Broadcast Flag
    q_flag := false //Quit Flag
    f_flag := false //Finish Flag
    var s_flag bool //Step Flag
    var cp_bcast int //CP Number Broadcasting
    var s_no uint32 //Session No.
    no_cp_res := 0 //No. of CPs Broadcasted/Re-Broadcasted 

    suite := nist.NewAES128SHA256P256()
    rand := suite.Cipher(abstract.RandomKey)

    x := suite.Scalar().Pick(rand) //CP private key
    y[cp_no - 1] = suite.Point().Mul(nil, x) //CP public key

    Y := suite.Point().Mul(nil, x) //Compound Public Key
    nr := make([][2]abstract.Point, n) //Noise Elgamal Blinding Factors
    nc := make([][2]abstract.Point, n) //Noise Elgamal Ciphers
    nr_o := make([][2]abstract.Point, n) //Shuffled Noise Elgamal Blinding Factors
    nc_o := make([][2]abstract.Point, n) //Shuffled Noise Elgamal Ciphers
    R := make([]abstract.Point, b+n) //Product of all CP Elgamal Blinding Factors
    C := make([]abstract.Point, b+n) //Product of all CP Elgamal Ciphers
    R_O := make([]abstract.Point, b+n) //Shuffled Elgamal Blinding Factors
    C_O := make([]abstract.Point, b+n) //Shuffled Elgamal Ciphers

    priv := new(Schnorrkey.Priv) //CP private key in bytes
    pub := new(Schnorrkey.Pub) //CP public key in bytes

    //Convert to Bytes
    priv.X = x.Bytes()
    var tb bytes.Buffer //Temporary Buffer
    y[cp_no - 1].MarshalTo(&tb)

    pub.Y = tb.Bytes()

    //Set Step No.
    step_no = 0

    //Set Broadcasting CP
    cp_bcast = 1
    
    //Set Broadcast Flag and Session No.
    if cp_no == 1 {

        b_flag = true
        s_no = 0
        for s_no == 0 {
            s_no = uint32(rnd.Int31()) //Set Session No. to Non-Zero Random Number
        }

    } else {

        b_flag = false
    }

    //Iterate over all IP counters
    for j := 0; j < b; j++ {
        k_j[j] = suite.Scalar().Zero() //Initialize with zero
        c_j[j] = suite.Scalar().Zero() //Initialize with zero
        R[j] = suite.Point().Null() //Initialize with identity element
        C[j] = suite.Point().Null() //Initialize with identity element
    }

    //Iterate over all Noise counters
    for j := 0; j < n; j++ {

        //Initialize 0 & 1 Ciphers
        nr[j][0] = suite.Point().Null() //Initialize with identity element
        nr[j][1] = suite.Point().Null() //Initialize with identity element
        nc[j][0] = suite.Point().Null() //Initialize with identity element
        nc[j][1] = suite.Point().Base() //Initialize with Base Point
    }

    fmt.Println("Started Server")

    //Listen to the TCP port
    sock := createServer(port)    
        
    for{
        //If Quit Flag not True
        if q_flag == false && f_flag == false {

            //If Broadcasting CP is Current CP and Broadcast Flag is set
            if cp_bcast == cp_no && b_flag == true {

                s_flag = false //Set Step Flag

                if step_no == 0 { //If Step Number is 0

                    cp_resp := new(CPres.Response)
                    cp_resp.R = make([][]byte, 1)

                    cp_resp.R[0] = make([]byte, 4) //Session No. in Bytes
                    binary.BigEndian.PutUint32(cp_resp.R[0], uint32(s_no)) //Convert to Bytes

                    //Convert to Bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    //Broadcast Public Key
                    broadcastData(suite, step_no, cp_no, cp_resp1, no_CPs)

                    s_flag = true //Set Step Flag

                } else if step_no == s_no + 1 { //If Step Number is 1
                
                    //Set CP Response to Broadcast Public Key
                    cp_resp := new(CPres.Response)
                    cp_resp.R = make([][]byte, 1)
                    cp_resp.Proof = make([][]byte, 1)
                    cp_resp.R[0] = pub.Y

                    //Create Proof
                    rep := proof.Rep("X", "x", "B")
                    secret := map[string]abstract.Scalar{"x": x}
                    public := map[string]abstract.Point{"B": suite.Point().Base(), "X": y[cp_no - 1]}
                    prover := rep.Prover(suite, secret, public, nil)
                    prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no)), rand, prover)
                    cp_resp.Proof[0] = make([]byte, len(prf))
                    copy(cp_resp.Proof[0][:], prf)

                    //Convert to Bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    //Broadcast Public Key
                    broadcastData(suite, step_no, cp_no, cp_resp1, no_CPs)

                    s_flag = true //Set Step Flag

                } else if step_no == s_no + 2 { //If Step Number is 2

                    cp_resp := new(CPres.Response) //CP Response
                    cp_resp.R = make([][]byte, 2 * n)
                    cp_resp.C = make([][]byte, 2 * n)
                    cp_resp.Proof = make([][]byte, n)

                    xbar, ybar, prover := par.MapElgamalCiphersChunked(shuffleNoise, nr, nc, Y, n) //Parallel Shuffle n Noise Coins
                       
                    //Iterate over all Noise Counters
                    for i := 0; i < n; i++ {

                        //Change its input as Shuffled Output for Next Verification
                        nr[i][0] = suite.Point().Set(xbar[i][0])
                        nr[i][1] = suite.Point().Set(xbar[i][1])
                        nc[i][0] = suite.Point().Set(ybar[i][0])
                        nc[i][1] = suite.Point().Set(ybar[i][1])

                        //Set CP Response to Broadcast Noise
                        tb.Reset() //Buffer Reset
                        xbar[i][0].MarshalTo(&tb)
                        cp_resp.R[2*i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[2*i][:], tb.Bytes()) //Convert to bytes                        

                        tb.Reset() //Buffer Reset
                        xbar[i][1].MarshalTo(&tb)
                        cp_resp.R[(2*i)+1] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[(2*i)+1][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer Reset
                        ybar[i][0].MarshalTo(&tb)
                        cp_resp.C[2*i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[2*i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer Reset
                        ybar[i][1].MarshalTo(&tb)
                        cp_resp.C[(2*i)+1] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[(2*i)+1][:], tb.Bytes()) //Convert to bytes

                        prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no))+strconv.Itoa(i), rand, prover[i])
                        cp_resp.Proof[i] = make([]byte, len(prf))
                        copy(cp_resp.Proof[i][:], prf)
                    }

                    //Convert to Bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    //Broadcast Shuffled Noise
                    broadcastData(suite, step_no, cp_no, cp_resp1, no_CPs)
 
                    //If Last CP has Broadcasted
                    if cp_bcast == no_CPs {

                        //Iterate Over all Noise Counters
                        for i := b; i < b+n; i++ {

                            //Select 1st Coin as Noise
                            R[i] = suite.Point().Set(nr[i-b][0])
                            C[i] = suite.Point().Set(nc[i-b][0])
                        }

                        b_flag = false //Don't set Step Flag and Set Broadcast Flag of All CPs to False (Nothing to do until DPs submit Responses!) 

                    } else {

                        s_flag = true //Set step Flag
                    }
                } else if step_no == s_no + 3 && m_flag == true { //If Step Number is 3

                    tmp := suite.Scalar() //temporary
                    cp_resp := new(CPres.Response) //CP Response
                    cp_resp.R = make([][]byte, b)
                    cp_resp.C = make([][]byte, b)
                    cp_resp.Proof = make([][]byte, b)

                    //Iterate over all Counters
                    for i := 0; i < b; i++ {

                        //Set CP Response to Broadcast Elgamal Ciphertext of Message Shares
                        tmp.Pick(rand)
                        tb.Reset() //Buffer Reset
		        r[i] = suite.Point().Mul(nil, tmp)
                        R[i].Add(R[i], r[i]) //Multiply Elgamal Bllinding Factors
                        _,_ = r[i].MarshalTo(&tb)
                        cp_resp.R[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[i][:], tb.Bytes()) //Convert to bytes
                        
                        tb.Reset() //Buffer Reset
                        c[i] = suite.Point().Mul(Y, tmp)
		        c[i].Add(c[i], suite.Point().Mul(nil, c_j[i]))
                        C[i].Add(C[i], c[i]) //Multiply Elgamal Ciphers
                        _,_ = c[i].MarshalTo(&tb)
                        cp_resp.C[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[i][:], tb.Bytes()) //Convert to bytes

                        //Create Proof
                        rep := proof.Rep("X", "x", "B")
                        secret := map[string]abstract.Scalar{"x": tmp}
                        public := map[string]abstract.Point{"B": suite.Point().Base(), "X": r[i]}
                        prover := rep.Prover(suite, secret, public, nil)
                        prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no))+strconv.Itoa(i), rand, prover)      
                        cp_resp.Proof[i] = make([]byte, len(prf))
                        copy(cp_resp.Proof[i][:], prf)
                    }

                    //Convert to Bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    //Broadcast Elgamal Ciphertexts
                    broadcastData(suite, step_no, cp_no, cp_resp1, no_CPs)

                    s_flag = true //Set Step Flag

                } else if step_no == s_no + 4 { //If Step Number is 4
                
                    Xbar, Ybar, prover := shuffle.Shuffle(suite, nil, Y, R, C, rand) //Shuffle Counters

                    //Assign to Output Vector and Convert to Bytes
                    cp_resp := new(CPres.Response) //CP Response
                    cp_resp.R = make([][]byte, b+n)
                    cp_resp.C = make([][]byte, b+n)
                    cp_resp.Proof = make([][]byte, 1)

                    prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no)), rand, prover)
                    cp_resp.Proof[0] = make([]byte, len(prf))
                    copy(cp_resp.Proof[0][:], prf)

                    //Iterate over all Counters
                    for i := 0; i < b+n; i++ {
                    
                        //Change its input as Shuffled Output for Next Verification
                        R[i] = suite.Point().Set(Xbar[i])
                        C[i] = suite.Point().Set(Ybar[i])
                   
                        tb.Reset() //Buffer Reset
                        Xbar[i].MarshalTo(&tb)
                        cp_resp.R[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[i][:], tb.Bytes()) //Convert to bytes
                    
                        tb.Reset() //Buffer Reset
                        Ybar[i].MarshalTo(&tb)
                        cp_resp.C[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[i][:], tb.Bytes()) //Convert to bytes
                    }

                    //Convert to Bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    //Broadcast Shuffled Counters
                    broadcastData(suite, step_no, cp_no, cp_resp1, no_CPs)

                    s_flag = true //Set Step Flag

                } else if step_no == s_no + 5 { //If Step Number is 5

                    s := make([]abstract.Scalar, b+n) //Randomness for Re-Encryption
                    q := make([]abstract.Scalar, b+n) //Randomness for Re-Randomization

                    //Iterate over all Counters
                    for i := 0; i < b+n; i++ {
              
                        s[i] = suite.Scalar().Pick(rand) //Pick a Random Scalar                   
                        q[i] = suite.Scalar().Zero()

                        for q[i].Equal(suite.Scalar().Zero()) == true {
                            q[i] = suite.Scalar().Pick(rand) //Set Exponent to Non-Zero Random Scalar
                        }
                    }

                    prf, Xbar, Ybar, _ := rerandomizeProofBatch(suite, R, C, nil, Y, s, q) //Re-Randomization

                    //Assign to Output Vector and Convert to Bytes
                    cp_resp := new(CPres.Response) //CP Response
                    cp_resp.R = make([][]byte, b+n)
                    cp_resp.C = make([][]byte, b+n)
                    cp_resp.Proof = make([][]byte, 1)

                    //Iterate over all Counters
                    for i := 0; i < b+n; i++ {

                        //Change its input as Rerandomized Output for Next Verification
                        R[i] = suite.Point().Set(Xbar[i])
                        C[i] = suite.Point().Set(Ybar[i])

                        tb.Reset() //Buffer Reset
                        Xbar[i].MarshalTo(&tb)
                        cp_resp.R[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer Reset
                        Ybar[i].MarshalTo(&tb)
                        cp_resp.C[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[i][:], tb.Bytes()) //Convert to bytes
                    }
            
                    //Convert Proof to Bytes
                    tb.Reset()
                    suite.Write(&tb, prf)
                    cp_resp.Proof[0] = make([]byte, len(tb.Bytes()))
                    copy(cp_resp.Proof[0][:], tb.Bytes())
                   
                    //Convert to Bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    //Broadcast Shuffled Counters
                    broadcastData(suite, step_no, cp_no, cp_resp1, no_CPs)

                    s_flag = true //Set Step Flag

                }  else if step_no == s_no + 6 { //If Step Number is 6

                    u := make([]abstract.Scalar, b+n) //Secret for Decryption
                    p := make([]abstract.Point, b+n) //Base Vector

                    //Iterate over all Counters
                    for i := 0; i < b+n; i++ {

                        u[i] = suite.Scalar().Set(x) //Set Secret for Decryption
                        p[i] = suite.Point().Base()
                    }
                    prf, _, Ybar, _ := proof.NewDLEQProofBatch(suite, p, R, u) //Decryption

                    //Assign to Output Vector and Convert to Bytes
                    cp_resp := new(CPres.Response) //CP Response
                    cp_resp.R = make([][]byte, b+n)
                    cp_resp.C = make([][]byte, b+n)
                    cp_resp.Proof = make([][]byte, 1)

                    //Iterate over all Counters
                    for i := 0; i < b+n; i++ {

                        //Change its input as Decrypted Output for Next Verification
                        C[i].Sub(C[i], Ybar[i])

                        tb.Reset() //Buffer Reset
                        R[i].MarshalTo(&tb)
                        cp_resp.R[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer Reset
                        C[i].MarshalTo(&tb)
                        cp_resp.C[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[i][:], tb.Bytes()) //Convert to bytes
                    }

                    //Convert Proof to Bytes
                    tb.Reset()
                    suite.Write(&tb, prf)
                    cp_resp.Proof[0] = make([]byte, len(tb.Bytes()))
                    copy(cp_resp.Proof[0][:], tb.Bytes())

                    //Convert to Bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    //Broadcast Shuffled Counters
                    broadcastData(suite, step_no, cp_no, cp_resp1, no_CPs)

                    if cp_bcast == no_CPs {
                        f_flag = true //Set Finish Flag
                        break
                    }

                    s_flag = true //Set Step Flag
                }

                if s_flag == true { //If Step Flag is Set

                    //Set Broadcast CP to Next CP
                    if cp_bcast == no_CPs {

                        step_no += 1
                        cp_bcast = 1                   

                    } else if cp_bcast != no_CPs && step_no != 0 {

                        cp_bcast = cp_no + 1
                    }

                    //If Step Number is 0
                    if step_no == 0 {

                        step_no = s_no + 1
                        time.Sleep(5*time.Second)
                    }

                    //Set Broadcast Flag of Next CP to True
                    if cp_no != cp_bcast {

                        b_flag = false

                    } else {

                        b_flag = true
                    }
                }
            } else { 

                fmt.Println("I am Here", step_no, cp_bcast, b_flag)

                //If Data is available
                if conn := acceptConnections(cp_no, sock); conn != nil {

                    //Parse Common Name
                    com_name := parseCommonName(conn)

                    //If Data Received from DP
                    if com_name[0:len(com_name)-1] == "DP" {

                        //Increment the number of DPs responded
                        dp_no = dp_no + 1

                        //Receive Data
                        buf := receiveData(conn)
                        conn.Close()
                        resp := new(DPres.Response)
                        proto.Unmarshal(buf, resp)

                        //Convert Bytes to Data
                        for i := 0; i < b; i++ {
                            tmp := suite.Scalar().SetBytes(resp.K[i]) 
                            k_j[i] = suite.Scalar().Add(k_j[i], tmp) //Add Key Share
                            tmp = suite.Scalar().SetBytes(resp.C[i])
                            c_j[i] = suite.Scalar().Add(c_j[i], tmp) //Add Message Share
                        }

                        //If all DPs have Responded
                        if dp_no == no_DPs {

                            //Add and Compute Share for Each Counter
                            for i := 0; i < b; i++ {
                                c_j[i] = suite.Scalar().Sub(c_j[i], k_j[i]) //Subtract Key Share from Message
                            }

                            //Set Message Flag
                            m_flag = true

                            //Set CP1 as Broadcasting CP
                            cp_bcast = 1

                            if cp_no == 1 {
                                b_flag = true //Set Broadcasting Flag of CP1
                            }
   
                            step_no += 1 //Increment Step No.
                        }
                    } else if com_name[0:len(com_name)-1] == "CP" {

                        buf := receiveData(conn)
                        conn.Close()
                        cp_resp := new(CPres.Response)

                        src,_ := strconv.Atoi(com_name[len(com_name)-1:]) //No. of CP that sent

                        //Verify Sign
                        l, f := verifyCPSign(suite, src, buf)

                        //Step No. in Message
                        t := binary.BigEndian.Uint32(buf[1:5])

                        //If Signature, Step No. and Broadcast Flag Verified
                        if t == step_no && f == true && uint8(buf[0]) == 1 {
                       
                            b_j[no_cp_res] = buf[9:9+l] //Store Signed Message
                            no_cp_res += 1 //Increment No. of CP Responses
                            proto.Unmarshal(buf[9+l:], cp_resp) //Store Message
                        }
                        
                        //Start Re-Broadcasting Phase
                        if no_cp_res == 1 {
                        
                            for i := 0; i < no_CPs; i++ { //Iterate over all CPs

                                if  i+1 == cp_bcast {

                                    continue //Broadcasting CP need not Wait for Anyone

                                } else if i+1 != cp_no {
                                    
                                    conn = acceptConnections(cp_no, sock)
                                    
                                    if conn != nil { //If Data is Available

                                        //Parse Common Name
                                        com_name = parseCommonName(conn)

                                        buf = receiveData(conn) //Read Data
                                        conn.Close()

                                        src,_ = strconv.Atoi(com_name[len(com_name)-1:]) //No. of CP that sent

                                        //Verify Sign
                                        l, f = verifyCPSign(suite, src, buf)

                                        //Step No. in Message
                                        t = binary.BigEndian.Uint32(buf[1:5])
                                      
                                        if t == step_no && f == true && uint8(buf[0]) == 0 && bytes.Compare(buf[9+l:], b_j[no_cp_res - 1]) == 0 {

                                            b_j[no_cp_res] = buf[9+l:] //Store Signed Message
                                            no_cp_res += 1

                                        } else {

                                            fmt.Print("Signatures Not Matching")
                                            q_flag = true 
                                            break
                                        }
                                    }
 
                                } else if i+1 == cp_no {
                                    
                                    fmt.Print("I am Re-broadcasting")
                                    time.Sleep(500*time.Millisecond)
                                    sendDataN_1(suite, step_no, cp_bcast, i+1, b_j[no_cp_res - 1], no_CPs)
                                }
                            }
                        }
                        
                        //If All CPs have finished Broadcasting/Re-Broadcasting
                        if no_cp_res == no_CPs - 1 {

                            //If Step No. is 0
                            if step_no == 0 {

                                s_no = binary.BigEndian.Uint32(cp_resp.R[0]) //Set Session No.

                            } else if step_no == s_no + 1 { //If Step No. is 1
                          
                                tmp := bytes.NewReader(cp_resp.R[0]) //Temporary
                                y[cp_bcast - 1] = suite.Point()
                                y[cp_bcast - 1].UnmarshalFrom(tmp)

                                //Verify Proof
                                rep := proof.Rep("X", "x", "B")
                                public := map[string]abstract.Point{"B": suite.Point().Base(), "X": y[cp_bcast - 1]}
                                verifier := rep.Verifier(suite, public)
                                err := proof.HashVerify(suite, strconv.Itoa(int(step_no)), verifier, cp_resp.Proof[0])

                                //If Error in Verifying
                                if err != nil {
                                    q_flag = true //Set Quit Flag
                                    break
                                }

                                //Multiply to create Compound Public Key
                                Y.Add(Y, y[cp_bcast - 1])

                            } else if step_no == s_no + 2 { //If Step No. 2


                                //Convert Bytes to Data
                                for i := 0; i < n; i++ {

                                    tmp := bytes.NewReader(cp_resp.R[2*i]) //Temporary
                                    nr_o[i][0] = suite.Point()
                                    nr_o[i][0].UnmarshalFrom(tmp) //Assign Shuffled Noise Elgamal Blinding Factors

                                    tmp = bytes.NewReader(cp_resp.R[(2*i)+1])
                                    nr_o[i][1] = suite.Point()
                                    nr_o[i][1].UnmarshalFrom(tmp) //Assign Shuffled Noise Elgamal Blinding Factors

                                    tmp = bytes.NewReader(cp_resp.C[2*i]) //Temporary
                                    nc_o[i][0] = suite.Point()
                                    nc_o[i][0].UnmarshalFrom(tmp) //Assign Shuffled Noise Elgamal Ciphers

                                    tmp = bytes.NewReader(cp_resp.C[(2*i)+1])
                                    nc_o[i][1] = suite.Point()
                                    nc_o[i][1].UnmarshalFrom(tmp) //Assign Shuffled Noise Elgamal Ciphers

                                    //Verify Proof
                                    verifier := shuffle.BiffleVerifier(suite, nil, Y, nr[i], nc[i], nr_o[i], nc_o[i])
                                    err := proof.HashVerify(suite, strconv.Itoa(int(step_no))+strconv.Itoa(i), verifier, cp_resp.Proof[i])

                                    //If Not Verified
                                    if err != nil {
                                        fmt.Print("Incorrect Proof")
                                        q_flag = true //Set Quit Flag
                                        break
                                    }
                                }

                                //Iterate over all Noise Counters
                                for i := 0; i < n; i++ {

                                    //Swap Current Output as Input
                                    nr[i][0] = suite.Point().Set(nr_o[i][0])
                                    nr[i][1] = suite.Point().Set(nr_o[i][1])
                                    nc[i][0] = suite.Point().Set(nc_o[i][0])
                                    nc[i][1] = suite.Point().Set(nc_o[i][1])
                                }

                                //If Last CP has Broadcasted
                                if cp_bcast == no_CPs {

                                    //Iterate Over all Noise Counters
                                    for i := b; i < b+n; i++ {

                                        //Select 1st Coin as Noise
                                        R[i] = suite.Point().Set(nr[i-b][0])
                                        C[i] = suite.Point().Set(nc[i-b][0])
                                    }
                                }
                            } else if step_no == s_no + 3 { //If Step No. 3

                                //Convert Bytes to Data
                                for i := 0; i < b; i++ {

                                    tmp := bytes.NewReader(cp_resp.R[i]) //Temporary
                                    tp := suite.Point() //Temporary
                                    tp.UnmarshalFrom(tmp)
                                    R[i].Add(R[i], tp) //Multiply Elgamal Blinding Factors

                                    //Verify Proof
                                    rep := proof.Rep("X", "x", "B")
                                    public := map[string]abstract.Point{"B": suite.Point().Base(), "X": tp}
                                    verifier := rep.Verifier(suite, public)
                                    err := proof.HashVerify(suite, strconv.Itoa(int(step_no))+strconv.Itoa(i), verifier, cp_resp.Proof[i])

                                    //If Error in Verifying
                                    if err != nil {
                                        q_flag = true //Set Quit Flag
                                        break
                                    }

                                    tmp = bytes.NewReader(cp_resp.C[i])
                                    tp = suite.Point()
                                    tp.UnmarshalFrom(tmp)
                                    C[i].Add(C[i], tp) //Multiply Elgamal Ciphers
                                }
                                
                            } else if step_no == s_no + 4 { //If Step No. 4

                                //Convert Bytes to Data
                                for i := 0; i < b+n; i++ {

                                    tmp := bytes.NewReader(cp_resp.R[i]) //Temporary
                                    R_O[i] = suite.Point()
                                    R_O[i].UnmarshalFrom(tmp) //Assign Shuffled Elgamal Blinding Factors

                                    tmp = bytes.NewReader(cp_resp.C[i])
                                    C_O[i] = suite.Point()
                                    C_O[i].UnmarshalFrom(tmp) //Assign Shuffled Elgamal Ciphers
                                }

                                //Verify Proof
                                verifier := shuffle.Verifier(suite, nil, Y, R, C, R_O, C_O)
                                err := proof.HashVerify(suite, strconv.Itoa(int(step_no)), verifier, cp_resp.Proof[0][:])

                                //If not verified
                                if err != nil {
                                    fmt.Println("Step 4 Proof Not Verified")
                                    q_flag = true //Set Quit Flag
                                    break
                                }

                                //Iterate over all Counters
                                for i := 0; i < b+n; i++ {

                                    //Swap Current Output as Input
                                    R[i] = suite.Point().Set(R_O[i])
                                    C[i] = suite.Point().Set(C_O[i])
                                }
                            } else if step_no == s_no + 5 { //If Step No. 5

                                prf := make([]*ReRandomizeProof, b+n)
                                tmp := bytes.NewReader(cp_resp.Proof[0])
                                suite.Read(tmp, prf)

                                //Convert Bytes to Data
                                for i := 0; i < b+n; i++ {

                                    tmp = bytes.NewReader(cp_resp.R[i]) //Temporary
                                    R_O[i] = suite.Point()
                                    R_O[i].UnmarshalFrom(tmp) //Assign Re-Randomized Elgamal Blinding Factors

                                    tmp = bytes.NewReader(cp_resp.C[i])
                                    C_O[i] = suite.Point()
                                    C_O[i].UnmarshalFrom(tmp) //Assign Re-Randomized Elgamal Ciphers

                                    //Verify Proof
                                    err := prf[i].Verify(suite, R[i], C[i], nil, Y, R_O[i], C_O[i])

                                    //If not verified
                                    if err != nil || R_O[i].Equal(suite.Point().Base()) == true || C_O[i].Equal(suite.Point().Base()) == true {
                                        fmt.Println("Step 5 Proof Not Verified")
                                        q_flag = true //Set Quit Flag
                                        break
                                    }
                                }

                                //Iterate over all Counters
                                for i := 0; i < b+n; i++ {

                                    //Swap Current Output as Input
                                    R[i] = R_O[i]
                                    C[i] = C_O[i]
                                }
                            } else if step_no == s_no + 6 { //If Step No. 6

                                prf := make([]*proof.DLEQProof, b+n)
                                tmp := bytes.NewReader(cp_resp.Proof[0])
                                suite.Read(tmp, prf)

                                //Convert Bytes to Data
                                for i := 0; i < b+n; i++ {

                                    tmp := bytes.NewReader(cp_resp.R[i]) //Temporary
                                    R_O[i] = suite.Point()
                                    R_O[i].UnmarshalFrom(tmp) //Assign Re-Randomized Elgamal Blinding Factors

                                    tmp = bytes.NewReader(cp_resp.C[i])
                                    C_O[i] = suite.Point()
                                    C_O[i].UnmarshalFrom(tmp) //Assign Re-Randomized Elgamal Ciphers

                                    //Verify Proof
                                    err := prf[i].Verify(suite, nil, R[i], y[cp_bcast - 1], suite.Point().Sub(C[i], C_O[i]))

                                    //If not verified
                                    if err != nil {
                                        fmt.Println("Step 6 Proof Not Verified")
                                        q_flag = true //Set Quit Flag
                                        break
                                    }
                                }
                               
                                //Iterate over all Counters
                                for i := 0; i < b+n; i++ {

                                    //Swap Current Output as Input
                                    C[i] = C_O[i]
                                }

                                if cp_bcast == no_CPs {
                                    f_flag = true //Set Finish Flag
                                    break
                                }
                            }

                            //If Last CP
                            if cp_bcast == no_CPs && step_no != s_no + 2 { //Step No. not 2 - Coz do nothing till DPs Respond!

                                step_no += 1 //Start Next Step Broadcast
                                cp_bcast = 1 //Set CP1 as Broadcasting CP
                     
                                //Set Broadcasting Flag of CP1 to true
                                if cp_no == 1 {

                                    b_flag = true
                                }
                            } else if cp_bcast != no_CPs && step_no != 0 {

                                cp_bcast += 1 //Set Broadcasting CP as next CP
                                
                                //Set Broadcasting Flag of Corresponding CP
                                if cp_bcast == cp_no {

                                    b_flag = true
                                }
                            } else if cp_bcast == no_CPs && step_no == s_no + 2 {
                           
                                b_flag = false //Do Nothing - Set Broadcast Flag of all CPs to False
                            }

                            if step_no == 0 {

                                step_no = s_no + 1 //Set Step No.

                                //Set CP1 as Broadcasting CP and Broadcast Flag to False
                                cp_bcast = 1
                                b_flag = false
                            }
                            no_cp_res = 0 //Set No. of CPs Broadcasted/Re-Broadcasted to 0
                        }
                    }
                }
            }
        } else {
            break
        } 
    }
    if q_flag == true {

        fmt.Println("Aborting")

    } else if f_flag == true {

        //Iterate over all Counters
        for i := 0; i < b+n; i++ {

            //If not g^0
            if e_f := C[i].Equal(suite.Point().Null()); e_f == false {

                //Add 1 to Aggregate
                agg += 1
            }
        }
        
        agg -= int64(n/2)

        fmt.Printf("Aggregate = %d \n", agg)
        fmt.Println("Finishing")        
    }
    os.Exit(0)
}

//Input: Command-line Arguments
//Output: CP Name, Port No.
//Function: Parse Command-line Arguments
func parseCommandline(arg []string) (int, string) {
    cp, _ := strconv.Atoi(os.Args[1]) //CP name
    port := "606" + os.Args[1] //port no.

    return cp, port
}

//Input: Data, Destination
//Function: Send Data to Destination
func sendDataToDest(data []byte, src int, dst int) {

    //Load Private Key and Certificate
    cert, err := tls.LoadX509KeyPair("certs/CP" + strconv.Itoa(src) + ".cert", "private/CP" + strconv.Itoa(src)  + ".key")
    checkError(err)

    //Dial TCP Connection
    config := tls.Config{Certificates: []tls.Certificate{cert}, InsecureSkipVerify: true}
    con,err := net.Dial("tcp", "localhost:606" + strconv.Itoa(dst))
    checkError(err)
   
    //Convert to TLS Connection
    file, err := con.(*net.TCPConn).File()
    err = syscall.SetsockoptInt(int(file.Fd()), syscall.SOL_SOCKET, syscall.SO_REUSEADDR, 1)
    conn := tls.Client(con, &config)

    l := make([]byte, 4) //Length of Data sent in bytes
    binary.BigEndian.PutUint32(l, uint32(len(data)))
    data = append(l, data...) //Append length to data
    _, err = conn.Write(data) //Send Data to Destination
    checkError(err)
}

//Input: Socket, Number of Bytes
//Output: Message Buffer
//Function: Read Exactly n Bytes from the Socket
func socketReadN(conn net.Conn, n uint32) []byte {
    buf := make([]byte, n)  
    _, err := io.ReadFull(conn,buf) //Read n Bytes
    checkError(err) 
    return buf
}

//Input: Socket
//Output: Message
//Function: Read Message from Socket
func receiveData(conn net.Conn) []byte {
    len_buf := socketReadN(conn, 4) //Read Message Length
    msg_len := binary.BigEndian.Uint32(len_buf) //Length of Message
    msg_buf := socketReadN(conn, msg_len) //Read Message 
    return msg_buf
}

//Input: Listener
//Output: Socket
//Function: Accept new connections in  Socket
func acceptConnections(cp int, listener net.Listener) *tls.Conn {
    //Create Server Socket
    cert, err := tls.LoadX509KeyPair("certs/CP"+ strconv.Itoa(cp) +".cert", "private/CP" + strconv.Itoa(cp) + ".key")
    checkError(err)

    //Add CA certificate to pool
    caCert, _ := ioutil.ReadFile("../CA/certs/ca.cert")
    caCertPool := x509.NewCertPool()
    caCertPool.AppendCertsFromPEM(caCert)

    //Create TLS Listener and Accept Connection
    config := tls.Config{Certificates: []tls.Certificate{cert}, ClientCAs: caCertPool, ClientAuth: tls.RequireAndVerifyClientCert,}
    conn, err := listener.Accept()
    file, err := conn.(*net.TCPConn).File()
    err = syscall.SetsockoptInt(int(file.Fd()), syscall.SOL_SOCKET, syscall.SO_REUSEADDR, 1)
    sock := tls.Server(conn, &config)

    return sock
}

//Input: CP Name, Port No.
//Output: Server Socket
//Function: Creates Server Socket
func createServer(port string) net.Listener {

    //Create TCP Listener
    listener, _ := net.Listen("tcp", "localhost:" + port)

    return listener
}

//Input: Cipher Suite, Step No., Source, Data, Number of CPs
//Function: Broadcast Data to All CPs
func broadcastData(suite abstract.Suite, step_no uint32, src int, data []byte, no_CPs int) {

    //Read Private Key from file
    in, err := ioutil.ReadFile("schnorr/private/cp" + strconv.Itoa(src) + ".priv")
    checkError(err)
    priv := &Schnorrkey.Priv{}
    err = proto.Unmarshal(in, priv)
    checkError(err)

    //Convert Bytes to Private Key
    x := suite.Scalar().SetBytes(priv.X)

    //Add Header
    b_s := make([]byte, 5)
    b_s[0] = byte(1) //Set Broadcast Flag
    binary.BigEndian.PutUint32(b_s[1:], step_no) //Set Step Number

    //Sign Message
    sign_msg, _ := sign.Schnorr(suite, x, data)
    l := make([]byte, 4) //Length of Signature
    binary.BigEndian.PutUint32(l, uint32(len(sign_msg))) //Set Length of Signature
    sign_msg = append(b_s, append(l, append(sign_msg, data...)...)...) //Add header and signature length

    //Iterate over all CPs
    for i := 0; i < no_CPs; i++ {
  
        //Send to all other CPs
        if i + 1 != src {
            sendDataToDest(sign_msg, src, i + 1)
        }
    } 
}

//Input: Cipher Suite, Step No. Source CP, CP that is sending, Data, Number of CPs
//Function: Send to All CPs but the Source
func sendDataN_1(suite abstract.Suite, step_no uint32, src int, cp int, data []byte, no_CPs int) {

    //Read Private Key from file
    in, _ := ioutil.ReadFile("schnorr/private/cp" + strconv.Itoa(cp) + ".priv")
    priv := &Schnorrkey.Priv{}
    proto.Unmarshal(in, priv)

    //Convert Bytes to Private Key
    x := suite.Scalar().SetBytes(priv.X)

    //Add Header
    b_s := make([]byte, 5)
    b_s[0] = byte(0) //Set Broadcast Flag to 0
    binary.BigEndian.PutUint32(b_s[1:], step_no) //Set Step Number

    //Sign Message
    sign_msg, _ := sign.Schnorr(suite, x, data)
    l := make([]byte, 4) //Length of Signature
    binary.BigEndian.PutUint32(l, uint32(len(sign_msg))) //Set Length of Signature
    sign_msg = append(b_s, append(l, append(sign_msg, data...)...)...) //Add header, step no. and signature length

    //Iterate over all CPs
    for i := 0; i < no_CPs; i++ {

        //Send to other n-1 CPs
        if i + 1 != cp && i + 1 != src {
                sendDataToDest(sign_msg, cp, i+1)
        }
    }
}

//Input: Cipher Suite, CP that is sending, Data, Broadcast Flag
//Output: Length of Signed Message and Bool(Verified / Not)
//Function: Verrify Sign
func verifyCPSign(suite abstract.Suite, src int, data []byte) (uint32, bool) {

    //Read Source Public Key from file
    in, _ := ioutil.ReadFile("schnorr/public/cp" + strconv.Itoa(src) + ".pub")
    buf := &Schnorrkey.Pub{}
    proto.Unmarshal(in, buf)

    y := bytes.NewReader(buf.Y) //Source public key in bytes
    src_pub := suite.Point() //Source public key
    src_pub.UnmarshalFrom(y)

    //Parse Source CP Signed Message
    ls := binary.BigEndian.Uint32(data[5:9]) //Length of Signed Message
    msg := data[9:9+ls] //Signed Message

    //Verify Signed Message
    err := sign.VerifySchnorr(suite, src_pub, data[9+ls:], msg)

    var f bool //Falg to be returned    

    if err == nil {
        f = true
    } else {
        f = false
        fmt.Print(err)
    }

    return ls, f
}

//Input: Points, Points
//Output: Shuffled Noise
//Function: Shuffle Noise
func shuffleNoise(x, y [2]abstract.Point, Y abstract.Point) ([2]abstract.Point, [2]abstract.Point, proof.Prover) {

    suite := nist.NewAES128SHA256P256()
    rand := suite.Cipher(abstract.RandomKey)

    xbar, ybar, proof := shuffle.Biffle(suite, nil, Y, x, y, rand) //Shuffle Noise Vectors

    return xbar, ybar, proof
}

//Input: Client Socket
//Output: Common Name
//Function: Parse Common Name from Certificate 
func parseCommonName(conn net.Conn) string {
    var com_name string //Common Name
    tlscon, ok := conn.(*tls.Conn)

    //If TLS connection
    if ok {
        tlscon.Handshake()
        for _, v := range tlscon.ConnectionState().PeerCertificates {
            com_name = v.Subject.CommonName //Get Common Name
        }
    }    

    return com_name
}

//rerandomizeProof computes a new NIZK proof for the scalars s and q with
//respect to base points A and B and publicly known points G and H. It therefore randomly selects commitments t1 and t2
//and then computes the challenge c = H(q(sG+A),q(sH+B),t1A+t2G,t1B+t2H) and responses r1 = qc+t1 and r2 = sqc + t2.
//Besides the proof, this function also returns the re-randomized and re-encrypted base points A1 = q(sG+A)
//and B1 = q(sG+B).
func rerandomizeProof(suite abstract.Suite, A, B, G, H abstract.Point, s, q abstract.Scalar) (proof *ReRandomizeProof, A1 abstract.Point, B1 abstract.Point, err error) {

    // Re-Encrypt Base Points
    A1 = suite.Point().Add(A, suite.Point().Mul(G, s))
    B1 = suite.Point().Add(B, suite.Point().Mul(H, s))

    // Re-Randomize Base Points
    A1.Mul(A1, q)
    B1.Mul(B1, q)

    // Commitment
    t1 := suite.Scalar().Pick(random.Stream)
    t2 := suite.Scalar().Pick(random.Stream)
    T1 := suite.Point().Mul(A, t1)
    T2 := suite.Point().Mul(B, t1)
    T1.Add(T1, suite.Point().Mul(G, t2))
    T2.Add(T2, suite.Point().Mul(H, t2))

    // Challenge
    cb, err := hash.Structures(suite.Hash(), A1, B1, T1, T2)
    if err != nil {
        return nil, nil, nil, err
    }
    c := suite.Scalar().Pick(suite.Cipher(cb))

    // Response
    r1 := suite.Scalar().Mul(q, c)
    r2 := suite.Scalar().Mul(s, r1)
    r1 = r1.Add(r1, t1)
    r2 = r2.Add(r2, t2)
        
    return &ReRandomizeProof{c, r1, r2, T1, T2}, A1, B1, nil
}

// ReRandomizeProofBatch computes lists of NIZK re-randomize proofs and of
// encrypted base points A1 and B1. Note that the challenge is computed over all
// input values.
func rerandomizeProofBatch(suite abstract.Suite, A, B []abstract.Point, G, H abstract.Point, s, q []abstract.Scalar) (proof []*ReRandomizeProof, A1 []abstract.Point, B1 []abstract.Point, err error) {
    if len(A) != len(B) || len(q) != len(s) || len(A) != len(s) {
        return nil, nil, nil, errors.New("inputs of different lengths")
    }

    n := len(s)
    proofs := make([]*ReRandomizeProof, n)
    t1 := make([]abstract.Scalar, n)
    t2 := make([]abstract.Scalar, n)
    T1 := make([]abstract.Point, n)
    T2 := make([]abstract.Point, n)
    A1 = make([]abstract.Point, n)
    B1 = make([]abstract.Point, n)

    for i := 0; i < n; i++ {

         // Re-Encrypt Base Points
         A1[i] = suite.Point().Add(A[i], suite.Point().Mul(G, s[i]))
         B1[i] = suite.Point().Add(B[i], suite.Point().Mul(H, s[i]))

         // Re-Randomize Base Points
         A1[i].Mul(A1[i], q[i])
         B1[i].Mul(B1[i], q[i])

         // Commitment
         t1[i] = suite.Scalar().Pick(random.Stream)
         t2[i] = suite.Scalar().Pick(random.Stream)
         T1[i] = suite.Point().Mul(A[i], t1[i])
         T2[i] = suite.Point().Mul(B[i], t1[i])
         T1[i].Add(T1[i], suite.Point().Mul(G, t2[i]))
         T2[i].Add(T2[i], suite.Point().Mul(H, t2[i]))
    }

    // Challenge
    cb, err := hash.Structures(suite.Hash(), A1, B1, T1, T2)
    if err != nil {
        return nil, nil, nil, err
    }
    c := suite.Scalar().Pick(suite.Cipher(cb))

    // Responses
    for i := 0; i < n; i++ {
        r1 := suite.Scalar().Mul(q[i], c)
        r2 := suite.Scalar().Mul(s[i], r1)
        r1 = r1.Add(r1, t1[i])
        r2 = r2.Add(r2, t2[i])
        proofs[i] = &ReRandomizeProof{c, r1, r2, T1[i], T2[i]}
    }

    return proofs, A1, B1, nil
}


// Verify examines the validity of the NIZK re-randomize proof.
// The proof is valid if the following two conditions hold:
//   r1A + r2G == cA1 + T1
//   r1B + r2H == cB1 + T2
func (p *ReRandomizeProof) Verify(suite abstract.Suite, A, B, G, H abstract.Point, A1, B1 abstract.Point) error {
    r1A := suite.Point().Mul(A, p.R1)
    r1B := suite.Point().Mul(B, p.R1)
    r2G := suite.Point().Mul(G, p.R2)
    r2H := suite.Point().Mul(H, p.R2)
    cA1 := suite.Point().Mul(A1, p.C)
    cB1 := suite.Point().Mul(B1, p.C)
    a := suite.Point().Add(r1A, r2G)
    b := suite.Point().Add(cA1, p.T1)
    c := suite.Point().Add(r1B, r2H)
    d := suite.Point().Add(cB1, p.T2)

    if !(a.Equal(b) && c.Equal(d)) {
        return errors.New("invalid proof")
    }

    return nil
}

//Input: Error
//Function: Check Error
func checkError(err error){
	if err != nil {
		fmt.Fprintf(os.Stderr, "Fatal error: %s", err.Error())
		os.Exit(1)
	}
}
