// std
use std::path::PathBuf;
// crates.io
use bitcoin::Network;
use clap::{
	builder::{
		styling::{AnsiColor, Effects},
		Styles,
	},
	ArgGroup, Parser, ValueEnum,
};
// atomicalsir
use crate::{engine::*, prelude::*, util::FeeBound};

#[derive(Debug, Parser)]
#[command(
	version = concat!(
		env!("CARGO_PKG_VERSION"),
		"-",
		env!("VERGEN_GIT_SHA"),
		"-",
		env!("VERGEN_CARGO_TARGET_TRIPLE"),
	),
	about,
	rename_all = "kebab",
	styles = styles(),
)]
#[clap(group = ArgGroup::new("engine").required(true))]
pub struct Cli {
	/// Use Rust native miner.
	///
	/// Need to provide a path to the atomicals-js repository's wallets directory.
	#[arg(long, group = "engine")]
	rust_engine: Option<PathBuf>,
	/// Use official atomicals-js miner.
	///
	/// Need to provide a path to the atomicals-js repository's directory.
	#[arg(long, value_name = "PATH", group = "engine")]
	js_engine: Option<PathBuf>,
	/// Thread count.
	///
	/// This adjusts the number of threads utilized by the Rust engine miner.
	#[arg(long, value_name = "NUM_THREADS", default_value_t = num_cpus::get() as u16)]
	num_threads: u16,
	/// Network type.
	#[arg(value_enum, long, value_name = "NETWORK", default_value_t = Network_::Mainnet)]
	network: Network_,
	/// Set the fee rate range to sat/vB.
	#[arg(long, value_name = "MIN,MAX", value_parser = FeeBound::from_str)]
	fee_bound: FeeBound,
	/// Specify the URI of the electrumx.
	#[arg(
		verbatim_doc_comment,
		long,
		value_name = "URI",
		default_value_t = String::from("https://ep.atomicals.xyz/proxy")
	)]
	electrumx: String,
	/// Ticker of the network to mine on.
	#[arg(long, value_name = "NAME")]
	ticker: String,
	/// Mine with the current actual bitwork otherwise use the next by default.
	#[arg(long, value_name = "CURRENT")]
	current: bool,
	/// Previous commit payload unix timestamp.
	#[arg(long, value_name = "COMMIT_TIMESTAMP")]
	commit_time: u64,
	/// Previous commit payload nonce.
	#[arg(long, value_name = "COMMIT_NONCE")]
	commit_nonce: u64,
	/// Previous commit transaction id.
	#[arg(long, value_name = "COMMIT_TXID")]
	commit_txid: String,
	/// Previous commit tx first output script pub key.
	#[arg(long, value_name = "COMMIT_SCRIPT_PUBKEY")]
	commit_scriptpk: String,
	/// Previous commit output spend(in sats, 1 btc = 100,000,000 sats).
	#[arg(long, value_name = "COMMIT_SPEND")]
	commit_spend: u64,
	/// Previous commit output refund(in sats, 1 btc = 100,000,000 sats).
	#[arg(long, value_name = "COMMIT_REFUND")]
	commit_refund: u64,
	/// Previous commit bitworkc, used under perpetual/infinite mint mode
	#[arg(long, value_name = "COMMIT_BITWORKC")]
	commit_bitworkc: Option<String>,
}
impl Cli {
	pub async fn run(self) -> Result<()> {
		let Cli {
			rust_engine,
			js_engine,
			num_threads,
			network,
			fee_bound,
			electrumx,
			ticker,
			current,
			commit_time,
			commit_nonce,
			commit_txid,
			commit_scriptpk,
			commit_spend,
			commit_refund,
			commit_bitworkc,
		} = self;
		let ticker = ticker.to_lowercase();

		if let Some(d) = js_engine {
			js::run(network.as_atomical_js_network(), &fee_bound, &electrumx, &d, &ticker).await?;
		} else if let Some(d) = rust_engine {
			rust::run(
				num_threads,
				network.into(),
				&fee_bound,
				&electrumx,
				&d,
				&ticker,
				current,
				commit_time,
				commit_nonce,
				&commit_txid,
				&commit_scriptpk,
				commit_spend,
				commit_refund,
				commit_bitworkc,
			)
			.await?;
		}

		Ok(())
	}
}

#[derive(Clone, Debug, ValueEnum)]
enum Network_ {
	Mainnet,
	Testnet,
}
impl Network_ {
	fn as_atomical_js_network(&self) -> &'static str {
		match self {
			Network_::Mainnet => "livenet",
			Network_::Testnet => "testnet",
		}
	}
}
impl From<Network_> for Network {
	fn from(v: Network_) -> Self {
		match v {
			Network_::Mainnet => Network::Bitcoin,
			Network_::Testnet => Network::Testnet,
		}
	}
}

fn styles() -> Styles {
	Styles::styled()
		.header(AnsiColor::Red.on_default() | Effects::BOLD)
		.usage(AnsiColor::Red.on_default() | Effects::BOLD)
		.literal(AnsiColor::Blue.on_default() | Effects::BOLD)
		.placeholder(AnsiColor::Green.on_default())
}
