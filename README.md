<div align="center">

# DISCLAIMER AND TERMS

## This is a workaround ONLY for the commit-success-but-reveal-failure transactions executed by the miratomicals-rac rust-engine. The failed transactions coming from atomicals-js are not supported at this time. Please be aware that this product/tool has been built in haste with very limited testing. Use it at your own discretion.

## The product is provided 'AS IS', without warranty of any kind, express or implied, including but not limited to the warranties of merchantability, fitness for a particular purpose and non-infringement. In no event shall the creators, authors or copyright holders be liable for any claim, damages or other liability, whether in an action of contract, tort or otherwise, arising from, out of or in connection with The Product or the use or other dealings in The Product. The Product does not represent any investment, security, financial instrument, redemption, promise, bearer instrument or commitment of any kind. The Product is intended only for educational and experimentation purposes only and is not backed or supported by any individual or team. There are no future prospects or plans of any kind beyond the educational and experimentation usages of The Product. Any use or interaction with The Product is expressly prohibited unless your jurisdiction and circumstances explicitly permits the use and interaction with The Product. Any interaction with The Product constitutes acceptance of these terms and the user accepts all responsibility and all risks associated with the use and interaction with The Product.

</div>

## Usage
```
Miraland miratomicals-rac Tool for Resuming after Commit Succeeded but Reveal Failed (based on miratomicals-rac).

Usage: miratomicals-rac [OPTIONS] --ticker <NAME> <--rust-engine <RUST_ENGINE>|--js-engine <PATH>> --commit-time <COMMIT_TIMESTAMP> --commit-nonce <COMMIT_NONCE> --commit-txid <COMMIT_TXID> --commit-scriptpk <COMMIT_SCRIPT_PUBKEY> --commit-spend <COMMIT_SPEND_SATS> --commit-refund <COMMIT_REFUND_SATS>

Options:
      --rust-engine <RUST_ENGINE>
          Use Rust native miner.

          Need to provide a path to the atomicals-js repository's wallets directory.

      --js-engine <PATH>
          Use official atomicals-js miner.

          Need to provide a path to the atomicals-js repository's directory.

      --num-thread <NUM_THREADS>
          Thread count.

          This adjusts the number of threads utilized by the Rust engine miner.

          [default: 16]

      --network <NETWORK>
          Network type

          [default: mainnet]
          [possible values: mainnet, testnet]

      --fee-bound <MIN,MAX>
          Set the fee rate range to sat/vB

      --electrumx <URI>
          Specify the URI of the electrumx.

          Example:
          - https://ep.atomicals.xyz/proxy

          [default: https://ep.atomicals.xyz/proxy]

      --ticker <NAME>
          Ticker of the network to mine on

      --commit-time <COMMIT_TIMESTAMP>
          Previous commit payload unix timestamp

      --commit-nonce <COMMIT_NONCE>
          Previous commit payload nonce

      --commit-txid <COMMIT_TXID>
          Previous commit transaction id

      --commit-scriptpk <COMMIT_SCRIPT_PUBKEY>
          Previous commit tx first output script pubkey

      --commit-spend <COMMIT_SPEND>
          Previous commit output spend(in sats, 1 btc = 100,000,000 sats)

      --commit-refund <COMMIT_REFUND>
          Previous commit output refund(in sats, 1 btc = 100,000,000 sats)

      --commit-bitworkc <COMMINT_BITWORKC>
          Optional, previous commit bitworkc, used in perpetual/infinite mint mode.

  -h, --help
          Print help (see a summary with '-h')

  -V, --version
          Print version
```

Special consideration [1]: In ```fixed``` mint mode, once max mints has been reached, the reveal will not be possible, the mint amount will be refunded to your original funding wallet, with the exception of the transaction fee, which will be paid to the miners as scheduled.

Special consideration [2]: In ```perpetual``` or ```infinite``` mint mode, if you resume a failed transaction after mining has entered the next round, resuming may not work because mint_bitworkc_current and mint_bitworkc_next values have changed. In this situation, refund will be the next action.

## Where to find above argument values?

--commit-time, --commit-nonce, please see console output, just looking for the line containing some pattern like ```payload time: (number)  payload nonce: (number)```.

--commit-txid, please search and find ```commit txid``` or ```commit tx``` in console log.

--commit-scriptpk, --commit-spend, --commit-refund can be found by searching your txid at https://mempool.space, please see screenshots below
### ATTENTION: --commit-spend, --commit-refund is in sats, so you need multiply the btc amount by 100,000,000

For --commit-scriptpk:
![Transaction Overview](/assets/images/tx-overview.png "Transaction Overview")

For --commit-spend and --commit-refund:
![Transaction Details](/assets/images/tx-details.png "Transaction Details")

For --commit-bitworkc, please search and find ```payload bitworkc``` in console log if mint mode is ```perpetual``` or ```infinite```

### Warning
The Rust mining engine is not fully tested; use at your own risk.

#### Example
```sh
RUST_LOG=miratomicals-rac=debug cargo r -r -- --rust-engine .maintain/atomicals-js/wallets --network testnet --electrumx https://eptestnet.atomicals.xyz/proxy --ticker miratomicalsir4
```

#### [Bitcoin testnet result](https://mempool.space/testnet/tx/aabbcc683171c11c3513f88f0c601e2657982e07d4e9259c8cfa4d909eb397bc)
```
yarn cli get 1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8bi0
yarn run v1.22.21
$ node dist/cli.js get 1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8bi0
walletPath ./wallets/wallet.json
{
  "global": {
    "coin": "BitcoinTestnet",
    "network": "testnet",
    "height": 2571723,
    "block_tip": "000000000000000ac41f551432d9f4bbc9a0fe5bbff561a32731ab1dd4da898b",
    "server_time": "2024-01-08T19:47:27.900342",
    "atomicals_block_tip": "0d40515d97e5b5185d055da4a3c8cb79a16f4e42dafda39b63729cc6698245ea",
    "atomical_count": 744,
    "atomicals_block_hashes": {
      "2571714": "b3b94255efd2d94ba70ec77cb298cb34e9b5a70a3e23ca04f12cabad142e0b71",
      "2571715": "caac375454e2006bd771d32df1b3918031f43397d61846b46764a1bb474d4394",
      "2571716": "48549f761486125b5be154b0f57bdf121e3c51f2703c8817188d6334fdac5a12",
      "2571717": "e01485011c133fb0933c0943efa87e0d566cd2d45724657eced1c106d8c1f7da",
      "2571718": "8e0fe1f6323f8b78bcdef48ca73733464412259876dfef0d32b409d4b02716f5",
      "2571719": "281f004f508ac251aa383746c606bb99d666cb23891390eb0b7154ad88fe9ba5",
      "2571720": "21920c557f6c5a30acee33f42b6d38b49cd9b1fc355388d21672bf73b67bb8a4",
      "2571721": "4395aeda9c362ffc9624abb886bcd911f47ed76608643d012fd941c127ea3354",
      "2571722": "c2d92352cf6e11d89c382fec2605351355d1e16a80f7b98f21af2ac6663d8b45",
      "2571723": "0d40515d97e5b5185d055da4a3c8cb79a16f4e42dafda39b63729cc6698245ea"
    }
  },
  "result": {
    "atomical_id": "1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8bi0",
    "atomical_number": 743,
    "atomical_ref": "304vze7pk8ey405nmpsejtqyz7vm2zq0ewhp7hx7sdjs3trtke5gi0",
    "type": "FT",
    "confirmed": true,
    "mint_info": {
      "commit_txid": "1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8b",
      "commit_index": 0,
      "commit_location": "1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8bi0",
      "commit_tx_num": 68083224,
      "commit_height": 2571712,
      "reveal_location_txid": "8b40e05c14326ae372bf5f9f89e746446015376c25ab564d0b740468dd38af43",
      "reveal_location_index": 0,
      "reveal_location": "8b40e05c14326ae372bf5f9f89e746446015376c25ab564d0b740468dd38af43i0",
      "reveal_location_tx_num": 68083235,
      "reveal_location_height": 2571713,
      "reveal_location_header": "000000202198b97559f21c7288e03792fbf8e680ffed5a76b381b5a41b00000000000000acc3d6e71f6b523152e1aba92d3e802af5318f4f71557e5b392bc2e82be7a035e53f9c65874b6e19473878fa",
      "reveal_location_blockhash": "ba2dd3b0bb964ff88601e9367b8704ea9ba2fb54cc49e9253600000000000000",
      "reveal_location_scripthash": "6e36ddc9ec7b7906c84eb9687f61d0d397d19488dce7830af4e673c697940893",
      "reveal_location_script": "5120cef338caae67c64b2ec0865c7c997e74e0805f7c17fcad787b89acf5de28bbea",
      "reveal_location_value": 546,
      "args": {
        "time": 1704738727,
        "nonce": 6904474,
        "bitworkc": "1809",
        "max_mints": 499611,
        "mint_amount": 777,
        "mint_height": 0,
        "mint_bitworkc": "aabbcc",
        "request_ticker": "miratomicals-rac4"
      },
      "meta": {},
      "ctx": {},
      "$mint_bitworkc": "aabbcc",
      "$request_ticker": "miratomicals-rac4",
      "$bitwork": {
        "bitworkc": "1809",
        "bitworkr": null
      },
      "reveal_location_address": "tb1pemen3j4wvlryktkqsew8ext7wnsgqhmuzl7267rm3xk0th3gh04qr9wcec",
      "blockheader_info": {
        "version": 536870912,
        "prevHash": "000000000000001ba4b581b3765aedff80e6f8fb9237e088721cf25975b99821",
        "merkleRoot": "35a0e72be8c22b395b7e55714f8f31f52a803e2da9abe15231526b1fe7d6c3ac",
        "timestamp": 1704738789,
        "bits": 426658695,
        "nonce": 4202182727
      }
    },
    "subtype": "decentralized",
    "$max_supply": 388197747,
    "$mint_height": 0,
    "$mint_amount": 777,
    "$max_mints": 499611,
    "$mint_bitworkc": "aabbcc",
    "$bitwork": {
      "bitworkc": "1809",
      "bitworkr": null
    },
    "$ticker_candidates": [
      {
        "tx_num": 68083224,
        "atomical_id": "1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8bi0",
        "txid": "1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8b",
        "commit_height": 2571712,
        "reveal_location_height": 2571713
      }
    ],
    "$request_ticker_status": {
      "status": "verified",
      "verified_atomical_id": "1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8bi0",
      "note": "Successfully verified and claimed ticker for current Atomical"
    },
    "$request_ticker": "miratomicals-rac4",
    "$ticker": "miratomicals-rac4",
    "mint_data": {
      "fields": {
        "args": {
          "time": 1704738727,
          "nonce": 6904474,
          "bitworkc": "1809",
          "max_mints": 499611,
          "mint_amount": 777,
          "mint_height": 0,
          "mint_bitworkc": "aabbcc",
          "request_ticker": "miratomicals-rac4"
        },
        "name": "miratomicals-rac4",
        "image": "atom:btc:dat:115b57d4c16cf28a05f5b637a9dc422d576e10fca5a69e47eb8024d7abd13c18i0/image.png",
        "legal": {
          "terms": "Free"
        },
        "links": {
          "x": {
            "v": "https://x.com/AurevoirXavier"
          },
          "website": {
            "v": "https://github.com/hack-ink/miratomicals-rac"
          }
        }
      }
    }
  }
}

yarn cli wallets --balances --noqr
yarn run v1.22.21
$ node dist/cli.js wallets --balances --noqr
walletPath ./wallets/wallet.json
walletInfo result {
  success: true,
  data: {
    address: 'tb1pzvexmf6v30taky62fftyegejz8gtz3472e6rm4jmpswjjm0qq9hqe84j4h',
    scripthash: 'c714c3997bce0afc410c50f2c8fd84347cc156f0072203f9ca1a40f98baafe0b',
    atomicals_count: 1,
    atomicals_utxos: [ [Object], [Object], [Object] ],
    atomicals_balances: {
      '1809bfb8f69a1de200b5a5b2e96afef9f7417ee0772363c7a7cb6591eb1a9b8bi0': [Object]
    },
    total_confirmed: 2331,
    total_unconfirmed: 0,
    atomicals_confirmed: 2331,
    atomicals_unconfirmed: 0,
    regular_confirmed: 0,
    regular_unconfirmed: 0,
    regular_utxos: [],
    regular_utxo_count: 0,
    history: undefined
  }
}
```

### Installation
#### Install from `crates.io`
To install from `crates.io`, use the following command:
```sh
cargo install miratomicals-rac
```

#### Download the pre-built binary
You can download the pre-build binary from our [GitHub release](https://github.com/hack-ink/subalfred/releases)

#### Build from source code (requires the nightly Rust)
To build from the source code, use the following commands:

```sh
git clone https://hack-ink/miratomicals-rac
cd miratomicals-rac
cargo build --release
```

#### Step-by-step setup (rust-engine)
1. Follow the installation steps for [`miratomicals`](#installation).
2. Run the following command: `miratomicals-rac --rust-engine <PATH to the atomicals-js's wallets folder> --fee-bound 50,150 --ticker quark`

### Q&A
- **Where can I find the mining log?**

  You'll find the information in `stdout.log` and `stderr.log`, which are located in the current working directory.

- **How to setup multi-wallet?**

  To set up a multi-wallet, place the `*.json` wallet files in the `atomicals-js/wallets` directory.

- **How to use one stash address in multi-wallet mining?**

  Add a wallet with a `<NAME>` under the `imported` field of your `atomicals-js/wallets/x.json` file.

  Then, run the command `miratomicals-rac --stash <NAME> ..`.

  You `atomicals-js/wallets/x.json` file should looks like below:
  ```json
  {
  	"phrase": "..",
  	"primary": {
  		"address": "..",
  		"path": "m/86'/0'/0'/0/0",
  		"WIF": ".."
  	},
  	"funding": {
  		"address": "..",
  		"path": "m/86'/0'/0'/1/0",
  		"WIF": ".."
  	},
  	"imported": {
  		"<NAME>": {
  			"address": "..",
  			"WIF": ".."
  		}
  	}
  }
  ```

- **What are the differences of `average-first` and `wallet-first` mining strategies?**
  - The `average-first` strategy mines 12 times for each wallet in one loop.
  - The `wallet-first` strategy mines indefinitely, switching wallets until the current wallet has more than 12 unconfirmed transactions.

## Future plan
- [ ] Update and rebuild `atomicals-js` automatically.
- [ ] Implement wallet balance detection.
- [x] Implement a mining worker in pure Rust.
