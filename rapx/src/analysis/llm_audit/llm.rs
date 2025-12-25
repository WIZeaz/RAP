use anyhow::Result;
use rustc_hir::attrs::ReprAttr::ReprInt;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::fs;
use std::path::Path;
use toml;

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct Config {
    pub api_key: String,
    pub model: String,
    pub base_url: String,
    #[serde(default = "default_temperature")]
    pub temperature: f64,
}

fn default_temperature() -> f64 {
    0.3
}

#[derive(Serialize, Debug, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub enum MessageRole {
    System,
    User,
    Assistant,
    Tool,
}

#[derive(Serialize, Debug, Clone)]
pub struct Message {
    pub role: MessageRole,
    pub content: String,
}

impl Message {
    pub fn system(content: String) -> Self {
        Message {
            role: MessageRole::System,
            content: content,
        }
    }

    pub fn user(content: String) -> Self {
        Message {
            role: MessageRole::User,
            content: content,
        }
    }

    pub fn assistant(content: String) -> Self {
        Message {
            role: MessageRole::Assistant,
            content: content,
        }
    }

    pub fn from_json(content: serde_json::Value) -> Result<Self> {
        let role_str = content
            .get("role")
            .and_then(|r| r.as_str())
            .ok_or_else(|| anyhow::anyhow!("Missing 'role' field"))?;

        let role = match role_str {
            "system" => MessageRole::System,
            "user" => MessageRole::User,
            "assistant" => MessageRole::Assistant,
            "tool" => MessageRole::Tool,
            _ => return Err(anyhow::anyhow!("Unknown role: {}", role_str)),
        };

        let content_str = content
            .get("content")
            .and_then(|c| c.as_str())
            .ok_or_else(|| anyhow::anyhow!("Missing 'content' field"))?
            .to_string();
        Ok(Message {
            role,
            content: content_str,
        })
    }
}

#[derive(Serialize, Debug, Clone)]
pub struct MessageContext {
    pub messages: Vec<Message>,
}

#[derive(Debug, Clone)]
pub struct Response {
    pub raw: serde_json::Value,
    pub message: Message,
}

#[derive(Debug, Clone)]
pub struct Session {
    pub client: reqwest::Client,
    pub config: Config,
}

impl Session {
    pub fn new(config: Config) -> Self {
        let client = reqwest::Client::new();
        Session { client, config }
    }

    pub async fn call(&self, ctx: &MessageContext) -> Result<Response> {
        let builder = self
            .client
            .post(&self.config.base_url)
            .bearer_auth(&self.config.api_key)
            .json(&json!(
            {
                "model" : self.config.model,
                "messages" : ctx.messages,
                "temperature": self.config.temperature,
            }));

        let response = builder.send().await?;
        let response: serde_json::Value = response.json().await?;

        Ok(Response {
            raw: response.clone(),
            message: Message::from_json(response["choices"][0]["message"].clone())?,
        })
    }
}
